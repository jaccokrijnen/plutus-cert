# plutus-cert

Translation certification of [Plutus](https://github.com/input-output-hk/plutus) compiler passes in Coq.

# Status
Work in progress

# Reading

* [Translation Certification for Smart Contracts](https://arxiv.org/pdf/2201.04919.pdf) (Krijnen, J.O.G, Chakravarty, M.M., Keller, G. and Swierstra, W., FLOPS 2022): Translation relations for certifying Plutus compilations
* [Verified Compiler Optimisations](https://studenttheses.uu.nl/handle/20.500.12932/446) (Joris Dral, 2022 MSc thesis): Using step-indexed logical relations for verifying translation relations
* [Automatically Deriving Checkers for Compilation Verification ](https://studenttheses.uu.nl/handle/20.500.12932/43855) (Bart Remmers, 2023 MSc thesis): Generating decision procedures for translation relations

# Setup (Nix)
Run `nix develop`.

# Setup (Nix + coq-lsp + vs-code)
1. Run `nix develop` in a shell.
2. Run `code` in that same shell
3. Run `which coq-lsp`
4. Enter this path in vscode coq-lsp plugin settings.
