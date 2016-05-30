#!/bin/bash
shopt -s expand_aliases
source ~/.bashrc
isabelle build -v -d . -b paraTheory_Session
isabelle build -v -d . -b n_germanish_base_Session
isabelle build -v -d . -b n_germanish_lemma_on_inv__1_Session
isabelle build -v -d . -b n_germanish_lemma_on_inv__2_Session
isabelle build -v -d . -b n_germanish_lemma_on_inv__3_Session
isabelle build -v -d . -b n_germanish_lemma_invs_on_rules_Session
isabelle build -v -d . -b n_germanish_invs_on_inis_Session
isabelle build -v -d . -b n_germanish_Session
