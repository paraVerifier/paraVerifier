
# Requirement for sublanguage of murphi

## Overall requirements

1. All keywords must be in lower case.
2. Comment lines are not supported.
3. Unsupported statements: `clear`, `undifine`, `assert`, `error`, `alias`. In fact, now only support assignments, `if`s and `for`s. 
4. Unsupported grammers: local variables, functions, procedures.

## Type definitions

### Consts

Allow consts, mainly integer consts, which end with `;`, such as

```
const
  NODE_NUM : 3;
  DATA_NUM : 2;
```

### Types
Allow three kinds of types, `scalarset`s, `enum`s and `record`s.

Scalarsets must end with `;`, such as

```
NODE : 1..NODE_NUM;
```

Enums must end with `;`, such as

```
CACHE_STATE : enum {CACHE_I, CACHE_S, CACHE_E};
```

Records must end with `;`, as the fileds in them are. such as

```
NODE_STATE : record
  CacheState : CACHE_STATE;
  CacheData : DATA;
end;
```

## Var definitions
Every varaible must end with `;`, such as

```
var
  Home : NODE;
  Sta : STATE;
```

## Ruleset
Rulesets must be closed with `endruleset`; `end` should NOT be used to close rulesets. And a following `;` is required. e.g.

```
ruleset h: NODE; d: DATA do
...
endruleset;
```

## Startstate
Startstates must be closed with `endstartstate`; `end` should NOT be used to close startstates. A following `;` is also required. e.g.

```
startstate "Init"
...
endstartstate;
```

Name of the startstate is optional, and after the name, there could be a optional 'begin'.

Startstates in a ruleset are supported, but in fact, we will choose the lowest value of each parameter as the initializer of it. For example

```
const
  NODE_NUM : 3;
  DATA_NUM : 2;

type
  NODE : 1..NODE_NUM;
  DATA : 1..DATA_NUM;

...

ruleset h: NODE; d: DATA do
startstate "Init"
...
endstartstate;
endruleset;
```

In this example, both `h` and `d` will be set to value `1`.

## Rule
Rules must be closed with `endrule`; `end` should NOT be used to close rules. A following `;` is also required. A rule must be difined as

```
rule <string> <formula> ==> begin <statements> endrule;
```

Rules in rulesets are supported.

## Invariant
Invariants should end with a `;`. An invariant must be difined as

```
invariant <string> <formula>;
```

Invariants in rulesets are supported.

## Formula

All formulae in murphi are supported.

## Statement

1. Assignments must be ended with `;`, including the last or the only assignment statement.
2. `if` statements must be ended with `end` or `endif` and a following `;`
3. `for` statements must be ended with `end` or `endfor` and a following `;`

