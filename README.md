# paraVerifier
paraVerifier is an automatic framework for proving parameterized cache coherence protocols.

## Background
Parameterized verification of cache coherence protocols is an important but challenging research problem. We have developed an automatic framework paraVerifier to handle this research problem:

1. It first discovers auxiliary invariants and the corresponding causal relations between invariants and protocol rules from a small reference instance of the verified protocol;
2. The discovered invariants and causal relations can then be generalized into their parameterized form to automatically construct a formal proof to establish the correctness of the protocol.

paraVerifier has been successfully applied to a number of benchmarks.

## Requirements
1. [NuSMV](http://nusmv.fbk.eu/)
2. [Z3](https://github.com/Z3Prover/)
3. CMurphi 5.4.9
4. [Isabelle](http://isabelle.in.tum.de/)
5. OCaml and necessary libs, including ocaml-nox ocaml-native-compilers ocaml-doc ocaml-findlib oasis libpcre-ocaml-dev
6. opam
7. Necessary libs installed by opam, including utop core async yojson core_extended core_bench cohttp async_graphics cryptokit menhir
8. [Python2.7.6](https://www.python.org/)
9. Python lib: pexpect

## Installation
Modify config file for OCaml, usually at ~/.ocamlinit, add the lines

```
#use "topfind";;
#thread;;
#camlp4o;;
#require "core.top";;
#require "core.syntax";;
#require “async”;;
```

## Run an example
1. Browse the directory where paraVerifier is put
2. Configure and run server

    Modify the file `server/settings.py`, set the variables `SMV_PATH`, `MU_PATH`, `MU_INCLUDE`, which mean path of NuSMV, path of CMurphi and path of include dir of CMurphi respectively.

    ```
    cd server
    python server.py -v
    ```
3. Compile a small example from .m to .ml

    ```
    cd ../murphi2ocaml
    python gen.py -m murphi/mutualEx.m > ../examples/mutualEx.ml
    cp murphi/mutualEx.m ../examples/n_mutualEx.m
    ```

    remove the invariant definitions in file `../examples/n_mutualEx.m`.

    In fact, you can skip this step if you just want to test an example.

4. Compile .ml

    ```
    cd ../examples
    corebuild mutualEx.byte -pkg re2 -I src
    ```

    This should generate an executive file `mutualEx.byte`

5. Run the executive file `mutualEx.byte` to generate proof scripts in dir `n_mutualEx` automatically
6. Run the scripts with Isabelle, you should config the `isabelle` in your `~/.bashrc` file, then run `./run.sh`

## Experiments
We have applied ParaVerifier to a number of benchmarks:

| protocol | #rule | #inv | time/s | memory/MB | thy |
| :------: | :---: | :--: | :----: | :-------: | :-: |
| MESI | 3 | 3 | 3.33 | 148 | [MESI thy](https://github.com/paraVerifier/paraVerifier/tree/master/proof_scripts/mesi) |
| MOESI | 5 | 3 | 3.34 | 147 | [MOESI thy](https://github.com/paraVerifier/paraVerifier/tree/master/proof_scripts/moesi) |
| Germanish | 6 | 3 | 3.47 | 147 | [Germanish thy](https://github.com/paraVerifier/paraVerifier/tree/master/proof_scripts/germanish) |
| German 2000 | 13 | 52 | 48.20 | 158 | [German 2000 thy](https://github.com/paraVerifier/paraVerifier/tree/master/proof_scripts/german) |
| Flash* | 60 | 152 | 325.60 | 178 | [Flash* thy](https://github.com/paraVerifier/paraVerifier/tree/master/proof_scripts/flash_without_data) |
| Flash | 62 | 162 | 589.23 | 178 | [Flash thy](https://github.com/paraVerifier/paraVerifier/tree/master/proof_scripts/flash) |

<small>\* the version of flash without data property.</small>






