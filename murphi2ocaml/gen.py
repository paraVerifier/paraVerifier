#coding=utf-8

import re
import logging

from copy import deepcopy


class TypeDef(object):
    def __init__(self, text):
        # hash map of all constants
        self.consts = {}
        self.const_defs = []
        self.typedefs = []
        # value range of each type
        self.typenames = {}
        self.evaluate(text)
    
    def evalEnum(self, text):
        enums = re.findall(r'(\w*?)\s*:\s*enum\s*\{(.*?)\}\s*;', text, re.S)
        for name, vstr in enums:
            values = filter(lambda x: x, map(lambda y: y.strip(), vstr.split(',')))
            for v in values: self.consts[v] = 0
            self.const_defs += map(lambda v: 'let _%s = strc \"%s\"'%(v, v), values)
            self.typedefs.append('enum \"%s\" [%s];'%(
                name, 
                '; '.join(map(lambda x: '_%s'%x, values))
            ))
            self.typenames[name] = map(lambda x: '_%s'%x, values)

    def evalScalarset(self, text):
        scalarsets = re.findall(r'(\w*?)\s*:\s*(\w+?)\s*\.\.\s*(\w+?)\s*;', text, re.S)
        def const2num(v, text):
            return int(re.findall(r'%s\s*:\s*(\d+)\s*;'%v, text, re.S)[0])
        for name, v1, v2 in scalarsets:
            num1 = int(v1) if re.match(r'\d+', v1) else const2num(v1, text)
            num2 = int(v2) if re.match(r'\d+', v2) else const2num(v2, text)
            self.typedefs.append('enum \"%s\" (int_consts [%s]);'%(
                name,
                '; '.join(map(lambda x: str(x), range(num1, num2 + 1)))
            ))
            self.typenames[name] = map(lambda x: '(intc %d)'%x, range(num1, num2 + 1))

    def evalBool(self):
        self.const_defs += ['let _True = boolc true', 'let _False = boolc false']
        self.typedefs.append('enum "boolean" [_True; _False];')
        self.typenames['boolean'] = ['_False', '_True'];

    def evaluate(self, text):
        self.evalEnum(text)
        self.evalScalarset(text)
        self.evalBool()
        self.value = '%s\n\n%s'%(
            '\n'.join(self.const_defs),
            'let types = [\n%s\n]'%('\n'.join(map(lambda x: '  %s'%x, self.typedefs)))
        )








index = -1

class Record(object):
    def __init__(self, text, typenames):
        super(Record, self).__init__()
        self.typenames = typenames
        self.evaluate(text)

    def judgeRecord(self, n, p, v):
        if v in self.typenames:
            return '  [arrdef [(\"%s\", %s)] \"%s\"]'%(n, p, v)
        else:
            return '  record_def \"%s\" %s _%s'%(n, p, v)

    def handleArr(self, n, v):
        try:
            if v[:5] == 'array':
                global index
                pattern = re.compile(r'array\s*\[(.+)\]\s*of\s*(.+)')
                pattern2 = re.compile(r'array\s*\[(.+)\]\s*of\s*array\s*\[(.+)\]\s*of\s*(.+)')
                if pattern2.match(v):
                    index += 2
                    param1, param2, t = pattern2.findall(v)[0]
                    pds = '[paramdef "i%d" "%s"; paramdef "i%d" "%s"]'%(index - 1, param1, index, param2)
                elif pattern.match(v):
                    index += 1
                    param, t = pattern.findall(v)[0]
                    pds = '[paramdef "i%d" "%s"]'%(index, param)
                else:
                    logging.error('new type: %s'%v)
                return self.judgeRecord(n, pds, t)
            else:
                return self.judgeRecord(n, '[]', v)
        except:
            logging.error(v)
    
    def evaluate(self, text):
        records = []
        record_strs = re.findall(r'(\w*?)\s*:\s*record\s*(.+?)\s*end\s*;', text, re.S)
        for name, fields in record_strs:
            fields = map(
                lambda x: tuple(map(lambda y: y.strip(), x.split(':'))), 
                filter(lambda x: x.strip(), fields.split(';'))
            )
            values = map(
                lambda (name, t): self.handleArr(name, t),
                fields
            )
            values = 'let _%s = List.concat [\n%s\n]'%(name, ';\n'.join(values))
            records.append(values)
        self.value = '\n\n'.join(records)












class Vardef(object):
    def __init__(self, text, typenames):
        super(Vardef, self).__init__()
        self.typenames = typenames
        self.evaluate(text)

    def judgeRecord(self, n, p, v):
        if v in self.typenames:
            return '  [arrdef [(\"%s\", %s)] \"%s\"]'%(n, p, v)
        else:
            return '  record_def \"%s\" %s _%s'%(n, p, v)

    def handleArr(self, n, v):
        if v[:5] == 'array':
            global index
            pattern = re.compile(r'array\s*\[(.+)\]\s*of\s*(.+)')
            param, t = pattern.findall(v)[0]
            index += 1
            return self.judgeRecord(n, '[paramdef \"i%d\" \"%s\"]'%(index, param), t)
        else:
            return self.judgeRecord(n, '[]', v)
    
    def evaluate(self, text):
        vs = []
        var_str = re.findall(r'var\s+((?:\w*\s*:\s*.*?\s*;\s*)*)', text, re.S)[0]
        fields = map(
            lambda x: tuple(map(lambda y: y.strip(), x.split(':'))), 
            filter(lambda x: x.strip(), var_str.split(';'))
        )
        values = map(
            lambda (name, t): self.handleArr(name, t),
            fields
        )
        self.value = 'let vardefs = List.concat [\n%s\n]'%(';\n'.join(values))
















def analyzeParams(params):
    """
    @param params: as `i:Node; j:Node`
    @return a tuple as `{'i': 'Node', 'j': 'Node'}, '[paramdef "i" "Node"; paramdef "j" "Node"]'`
    """
    if not params:
        return {}, '[]'
    parts = params.split(';')
    param_name_dict = {}
    for p in parts: param_name_dict[p.split(':')[0].strip()] = p.split(':')[1].strip()
    param_defs = map(
        lambda x: 'paramdef ' + ' '.join(map(
            lambda y: '\"%s\"'%y.strip(), 
            x.strip().split(':'))
        ),
        parts
    )
    return param_name_dict, '[%s]'%('; '.join(param_defs))

def escape(name):
    return 'n_%s'%(re.sub(r'_+', '_', re.sub(r'[^a-zA-Z0-9]', '_', name).strip('_')))








class Formula(object):
    __PRIORITY = {
        '(': 100, '=': 50, '!=': 50, '!': 40, '&': 30, '|': 20, '->': 10
    }
    def __init__(self, text, param_names, consts):
        super(Formula, self).__init__()
        self.param_names = param_names
        self.consts = consts
        try:
            self.text = self.splitText(text)
            self.suffix = self.process(self.text)
            self.value = self.evaluate(self.suffix, self.param_names)
        except Exception, e:
            print e
            print text
            print self.text

    def splitText(self, text):
        dividers = r'(do|\sendforall|\sendexists|\send|\(|\)|=|!=|!|&|\||->)'
        parts = filter(lambda p: p, map(lambda x: x.strip(), re.split(dividers, text)))
        big_parts = []
        to_add = []
        exp_ends = 0
        for p in parts:
            if p.startswith(('forall', 'exists')):
                exp_ends += 1
                to_add.append(p)
            elif p.startswith('end'):
                exp_ends -= 1
                to_add.append('end')
                if exp_ends == 0:
                    big_parts.append(' '.join(to_add))
                    to_add = []
            elif exp_ends > 0:
                to_add.append(p)
            else:
                big_parts.append(p)
        if len(big_parts) == 0:
            print text
            print parts
            logging.error('could not split text: %s'%text)
        return big_parts

    def process(self, text):
        ops = []
        suffix = []
        for t in text:
            if t in self.__PRIORITY:
                while ops != [] and ops[-1] != '(' and self.__PRIORITY[t] <= self.__PRIORITY[ops[-1]]:
                    suffix.append(ops.pop())
                ops.append(t)
            elif t == ')':
                while ops[-1] != '(':
                    suffix.append(ops.pop())
                ops.pop()
            else:
                suffix.append(t)
        while ops != []:
            suffix.append(ops.pop())
        return suffix

    def evalVar(self, var):
        """
        'a[b][c].d.e[f]' -> 
        ['a[b][c]', 'd', 'e[f]'] -> 
        [['a', 'b', 'c'], ['d'], ['e', 'f']]
        """
        name_parts = map(
            lambda n: map(lambda x: x.strip(']'), n.split('[')), 
            var.split('.')
        )
        variables = map(
            lambda parts: 'global \"%s\"'%parts[0] if len(parts) == 1 else\
                'arr [(\"%s\", [%s])]' %(
                    parts[0], 
                    '; '.join(map(lambda p: 'paramref \"%s\"'%p, parts[1:]))
                ),
            name_parts
        )
        return '(%s)'%variables[0] if len(variables) == 1 else '(record [%s])'%('; '.join(variables))

    def evalAtom(self, atom, param_names):
        if atom in self.consts:
            return '(const _%s)'%atom
        elif atom in param_names:
            return '(param (paramref \"%s\"))'%atom
        elif re.match(r'^\d+$', atom):
            return '(const (intc %s))'%atom
        elif atom.lower() in ['true', 'false']:
            return '(const (boolc %s))'%atom.lower()
        elif re.match(r'^forall.*end$', atom) or re.match(r'^exists.*?end$', atom):
            if re.match(r'^forall.*end$', atom):
                params, text = re.findall(r'forall(.*?)do(.*)end', atom)[0]
            else:
                params, text = re.findall(r'exists(.*?)do(.*)end', atom)[0]
            param_name_dict, param_defs = analyzeParams(params)
            for p in param_names:
                if p not in param_name_dict: param_name_dict[p] = 0
            text = self.splitText(text)
            sub_form = self.evaluate(self.process(text), param_name_dict)
            if re.match(r'^forall.*?end$', atom):
                return '(forallFormula %s %s)'%(param_defs, sub_form)
            else:
                return '(existFormula %s %s)'%(param_defs, sub_form)
        else:
            return '(var %s)'%self.evalVar(atom)

    __RELATION_OP = {
        '&': '(andList [%s; %s])',
        '|': '(orList [%s; %s])',
        '->': '(imply %s %s)',
        '=': '(eqn %s %s)',
        '!=': '(neg (eqn %s %s))',
    }
    def evaluate(self, suffix, param_names):
        values = []
        for s in suffix:
            if s not in self.__PRIORITY:
                values.append((False, s))
            elif s in ['=', '!=']:
                right = self.evalAtom(values.pop()[1], param_names)
                left = self.evalAtom(values.pop()[1], param_names)
                values.append((True, self.__RELATION_OP[s]%(left, right)))
            elif s == '!':
                evaled, atom = values.pop()
                if evaled: val = '(neg %s)'%atom
                elif atom.strip()[:6] in ['forall', 'exists']:
                    val = '(neg %s)'%self.evalAtom(atom, param_names)
                else: val = '(eqn %s (const _False))'%self.evalAtom(atom, param_names)
                values.append((True, val))
            elif s in ['&', '|', '->']:
                def do_eval(evaled, atom):
                    if evaled: return atom
                    elif atom.strip()[:6] in ['forall', 'exists']:
                        return self.evalAtom(atom, param_names)
                    else: return '(eqn %s (const _True))'%self.evalAtom(atom, param_names)
                rval = do_eval(*values.pop())
                lval = do_eval(*values.pop())
                values.append((True, self.__RELATION_OP[s]%(lval, rval)))
            else:
                print self.text
                print suffix
                logging.error('unknown operator %s'%s)
        if values[0][0]: return values[0][1]
        elif values[0][1].strip()[:6] in ['forall', 'exists']:
            return self.evalAtom(values[0][1], param_names)
        else: return '(eqn %s (const _True))'%self.evalAtom(values[0][1], param_names)

















class Statement(object):
    def __init__(self, text, param_names, consts):
        super(Statement, self).__init__()
        self.param_names = param_names
        self.consts = consts
        self.statements = self.splitText(text)
        self.value = self.evaluate(self.statements, self.param_names, self.consts)

    def splitText(self, text):
        parts = filter(lambda p: p, map(lambda x: x.strip(), re.split(r'(;|do|then|else)', text)))
        big_parts = []
        to_add = []
        exp_ends = 0
        for p in parts:
            if p.startswith(('if', 'for')):
                exp_ends += 1
                to_add.append(p)
            elif p.startswith('end'):
                exp_ends -= 1
                to_add.append(p)
                if exp_ends == 0:
                    big_parts.append(' '.join(to_add))
                    to_add = []
            elif exp_ends > 0:
                to_add.append(p)
            elif p != ';':
                big_parts.append(p)
        if len(big_parts) == 0:
            for p in parts: print p
            logging.error('could not split text: %s'%text)
        return big_parts

    def evalVar(self, var):
        """
        'a[b][c].d.e[f]' -> 
        ['a[b][c]', 'd', 'e[f]'] -> 
        [['a', 'b', 'c'], ['d'], ['e', 'f']]
        """
        name_parts = map(
            lambda n: map(lambda x: x.strip(']'), n.split('[')), 
            var.split('.')
        )
        variables = map(
            lambda parts: 'global \"%s\"'%parts[0] if len(parts) == 1 else\
                'arr [(\"%s\", [%s])]' %(
                    parts[0], 
                    '; '.join(map(lambda p: 'paramref \"%s\"'%p, parts[1:]))
                ),
            name_parts
        )
        return '(%s)'%variables[0] if len(variables) == 1 else '(record [%s])'%('; '.join(variables))

    def evalAtom(self, atom, param_names):
        if atom in self.consts:
            return '(const _%s)'%atom
        elif atom in param_names:
            return '(param (paramref \"%s\"))'%atom
        elif re.match(r'^\d+$', atom):
            return '(const (intc %s))'%atom
        elif atom.lower() in ['true', 'false']:
            return '(const (boolc %s))'%atom.lower()
        else:
            return '(var %s)'%self.evalVar(atom)

    def partitionIf(self, statement):
        parts = filter(lambda p: p, map(lambda x: x.strip(), re.split(r'(;|do|then|else)', statement)))
        sub_clause = []
        to_add = []
        exp_ends = 0
        for p in parts:
            if p.startswith(('if', 'for', 'exists')):
                exp_ends += 1
                to_add.append(p)
            elif p.startswith(('elsif', 'else')) and exp_ends == 1:
                sub_clause.append(' '.join(to_add))
                to_add = [p]
            elif p.startswith('end'):
                exp_ends -= 1
                if exp_ends == 0:
                    sub_clause.append(' '.join(to_add))
                    to_add = []
                else:
                    to_add.append(p)
            elif exp_ends > 0:
                to_add.append(p)
            else:
                logging.error('should not exists statement out of if sub clause')
        return sub_clause

    def analyzeIf(self, sub_clause, param_names, consts):
        if sub_clause.startswith('if'):
            f, s = re.findall(r'if(.*?)then(.*)', sub_clause, re.S)[0]
            formula = Formula(f.strip(), param_names, consts)
            inner_ss = self.evaluate(self.splitText(s.strip()), param_names, consts)
            return formula.value, inner_ss
        elif sub_clause.startswith('elsif'):
            f, s = re.findall(r'elsif(.*?)then(.*)', sub_clause, re.S)[0]
            formula = Formula(f.strip(), param_names, consts)
            inner_ss = self.evaluate(self.splitText(s.strip()), param_names, consts)
            return formula.value, inner_ss
        elif sub_clause.startswith('else'):
            s = re.findall(r'else(.*)', sub_clause, re.S)[0]
            inner_ss = self.evaluate(self.splitText(s.strip()), param_names, consts)
            return (inner_ss, )
        else:
            logging.error('not a subclause of if statement: %s'%sub_clause)

    def evalIf(self, statement, param_names, consts):
        sub_clause = map(
            lambda s: self.analyzeIf(s, param_names, consts), 
            self.partitionIf(statement)
        )
        def inner(sc):
            try:
                if len(sc) == 1:
                    return '(ifStatement %s %s)'%sc[0]
                # ifelse语句的后半句不能是elsif
                elif len(sc) == 2 and len(sc[1]) == 1:
                    return '(ifelseStatement %s %s %s)'%(sc[0][0], sc[0][1], sc[1][0])
                elif len(sc) >= 2:
                    latter = inner(sc[1:])
                    return '(ifelseStatement %s %s %s)'%(sc[0][0], sc[0][1], latter)
                else:
                    logging.error('wrong subclause')
            except:
                msg = '\n'.join(map(lambda x: str(x), sub_clause))
                logging.error('wrong sub clause: \n%s\n\n%s\n\n'%(self.partitionIf(statement), msg))
        return inner(sub_clause)

    def evalFor(self, statement, param_names, consts):
        params, statement_str = re.findall(r'for(.*?)do(.*)end(?:for)*', statement, re.S)[0]
        param_name_dict, param_defs = analyzeParams(params)
        for p in param_names:
            if p not in param_name_dict: param_name_dict[p] = 0
        inner_ss = self.evaluate(self.splitText(statement_str), param_name_dict, consts)
        return '(forStatement %s %s)'%(inner_ss, param_defs)

    def evaluate(self, statements, param_names, consts):
        def inner(statement):
            if statement.startswith('if'):
                return self.evalIf(statement, param_names, consts)
            elif statement.startswith('for'):
                return self.evalFor(statement, param_names, consts)
            elif re.match(r'clear\s', statement):
                try:
                    estr = statement[5:]
                    return 'clear %s'%(self.evalVar(estr.strip()))
                except:
                    logging.error('unable to handle statement: %s'%statement)
            else:
                try:
                    vstr, estr = statement.split(':=')
                    v = self.evalVar(vstr.strip())
                    e = self.evalAtom(estr.strip(), param_names)
                    return '(assign %s %s)'%(v, e)
                except:
                    logging.error('unable to handle statement: %s'%statement)
        if len(statements) > 1:
            return '(parallel [%s])'%('; '.join(map(lambda s: inner(s), statements)))
        elif len(statements) == 1:
            return inner(statements[0])
        else:
            logging.error('no statement to be evaluated')






















class Rule(object):
    def __init__(self, text, params, param_names, consts):
        super(Rule, self).__init__()
        pattern = re.compile(r'rule\s*\"(.*?)\"\s*(.*?)==>.*?begin(.*?)endrule\s*;', re.S)
        self.name, guard, statements = pattern.findall(text)[0]
        self.name = escape(self.name)
        self.params = params
        self.param_names = param_names
        self.formula = Formula(guard, self.param_names, consts)
        self.statement = Statement(statements, self.param_names, consts)
        self.value = '''let %s =
  let name = \"%s\" in
  let params = %s in
  let formula = %s in
  let statement = %s in
  rule name params formula statement'''%(self.name, self.name, self.params, self.formula.value, self.statement.value)
























class RuleSet(object):
    def __init__(self, text, consts):
        super(RuleSet, self).__init__()
        rules = []
        rules += self.rulesets(text, consts)
        rules += self.singlerules(text, consts, map(lambda r: r.name, rules))
        self.value = '%s\n\nlet rules = [%s]'%(
            '\n\n'.join(map(lambda r: r.value, rules)), 
            '; '.join(map(lambda r: r.name, rules))
        )

    def rulesets(self, text, consts):
        rules = []
        pattern = re.compile(r'ruleset(.*?)do(.*?)endruleset\s*;', re.S)
        rulesets = pattern.findall(text)
        for params, rules_str in rulesets:
            param_name_dict, param_defs = analyzeParams(params)
            rule_texts = re.findall(r'(rule.*?endrule;)', rules_str, re.S)
            rules += map(lambda r: Rule(r, param_defs, param_name_dict, consts), rule_texts)
        return rules

    def singlerules(self, text, consts, ruleset_names):
        pattern = re.compile(r'(rule.*?endrule\s*;)', re.S)
        rule_texts = pattern.findall(text)
        rules = map(lambda r: Rule(r, [], {}, consts), rule_texts)
        return filter(lambda r: r.name not in ruleset_names, rules)











class StartState(object):
    def __init__(self, text, consts, typenames):
        super(StartState, self).__init__()
        init_p2 = r'startstate\s*(?:\".*?\"){0,1}(?:.*?begin){0,1}(.*?)endstartstate\s*;'
        init_p1 = r'ruleset\s*([\w :;]*)do\s*%s\s*endruleset\s*;'%init_p2
        if re.findall(init_p1, text, re.S):
            params, statements = re.findall(init_p1, text, re.S)[0]
        else:
            params, statements = '', re.findall(init_p2, text, re.S)[0]
        param_types, _ = analyzeParams(params)
        for k, v in param_types.items():
            param_types[k] = (v, typenames[v][0])
        statement = Statement(statements, param_types, consts)
        statement_value = statement.value
        for k, v in param_types.items():
            statement_value = statement_value.replace('param (paramref \"%s\")'%k, 
                'param (paramfix "%s" "%s" %s)'%(k, v[0],v[1]))
            statement_value = statement_value.replace('paramref \"%s\"'%k, 
                'paramfix "%s" "%s" %s'%(k, v[0],v[1]))
        self.value = 'let init = %s'%statement_value













class Invariant(object):
    def __init__(self, text, consts, typenames):
        super(Invariant, self).__init__()
        names = []
        invs = []
        invset_names, invset_invs = self.invsets(text, consts)
        names += invset_names
        invs += invset_invs
        inv_alone_names, inv_alone_invs = self.inv_alone(text, consts)
        names += inv_alone_names
        invs += inv_alone_invs
        self.value = '%s\n\nlet properties = [%s]'%('\n\n'.join(invs), '; '.join(names))

    def invsets(self, text, consts):
        pattern = r'ruleset\s*([\w :;]*)do\s*invariant\s*\"(.*?)\"\s*(.*?)\s*;{0,1}\s*endruleset\s*;'
        inv_strs = re.findall(pattern, text, re.S)
        invs = []
        names = []
        for params, name, form in inv_strs:
            param_name_dict, param_defs = analyzeParams(params)
            name = escape(name)
            formula = Formula(form, param_name_dict, consts)
            names.append(name)
            invs.append('''let %s =
  let name = \"%s\" in
  let params = %s in
  let formula = %s in
  prop name params formula'''%(name, name, param_defs, formula.value))
        return names, invs

    def inv_alone(self, text, consts):
        # TODO problems exist here
        pattern = r'[^do]+\s+invariant\s*\"(.*?)\"\s*(.*?)\s*;{0,1}'
        inv_strs = re.findall(pattern, text, re.S)
        invs = []
        names = []
        for name, form in inv_strs:
            print name, form
            name = escape(name)
            formula = Formula(form, [], consts)
            names.append(name)
            invs.append('''let %s =
  let name = "%s" in
  let params = [] in
  let formula = %s in
  prop name params formula'''%(name, name, formula.value))
        return names, invs










class Protocol(object):
    def __init__(self, name, filename):
        self.name = escape(name)
        f = open(filename, 'r')
        self.content = f.read()
        f.close()
        self.evaluate()

    def evaluate(self):
        types = TypeDef(self.content)
        records = Record(self.content, types.typenames)
        vardefs = Vardef(self.content, types.typenames)
        init = StartState(self.content, types.consts, types.typenames)
        rulesets = RuleSet(self.content, types.consts)
        invs = Invariant(self.content, types.consts, types.typenames)
        self.value = '''
(* This program is translated from its corresponding murphi version *)

open Core.Std
open Utils
open Paramecium
open Loach
open Formula
open InvFinder
open Cmdline\n\n%s\n\n%s\n\n%s\n\n%s\n\n%s\n\n%s\n\n
let protocol = {
  name = \"%s\";
  types;
  vardefs;
  init;
  rules;
  properties;
}\n\nlet () = run_with_cmdline (fun () ->
  let protocol = preprocess_rule_guard ~loach:protocol in
  let cinvs_with_varnames, relations = find protocol
    ~murphi:(In_channel.read_all "%s.m")
  in
  Isabelle.protocol_act protocol cinvs_with_varnames relations ()
)\n'''%(
    types.value, records.value, vardefs.value, init.value, 
    rulesets.value, invs.value, self.name, self.name)














import getopt
import sys
import os


help_msg = 'Usage: python gen.py [-n|-m|-h] for [--name|--murphi|--help]\n'

try:
    opts, args = getopt.getopt(sys.argv[1:], 'n:m:h', ['name=', 'murphi=', 'help'])
    name = None
    murphi = None
    for opt, arg in opts:
        if opt in ('-h', '--help'):
            sys.stdout.write(help_msg)
            sys.exit()
        elif opt in ('-n', '--name'):
            name = arg
        elif opt in ('-m', '--murphi'):
            murphi = arg
        else:
            sys.stderr.write(help_msg)
            sys.exit()
    if murphi is not None and os.path.isfile(murphi):
        basename = os.path.basename(murphi)
        if name is None:
            name = basename if len(basename.split('.')) == 1 else '.'.join(basename.split('.')[:-1])
        protocol = Protocol(name, murphi)
        print protocol.value
    else:
        sys.stderr.write(help_msg)
        sys.exit()
except getopt.GetoptError:
    sys.stderr.write(help_msg)
    sys.exit()
