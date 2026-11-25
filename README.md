# Lloyd C

Standalone command-line proof checker written in portable C11. It has no
third-party dependencies or interpreter runtime requirement.

## Windows build

Use either build script from this directory:

- `build_msvc.bat` from a Visual Studio Developer Command Prompt or Developer
  PowerShell, with a recent MSVC that supports C11.
- `build_mingw.bat` with MinGW-w64 GCC on `PATH`.

The equivalent commands are:

```bat
cl /nologo /std:c11 /W4 /D_CRT_SECURE_NO_WARNINGS lloyd.c /Fe:lloyd.exe
```

```bat
gcc -std=c11 -O2 -Wall -Wextra -Wpedantic lloyd.c -o lloyd.exe
```

Run it in PowerShell:

```powershell
.\build_mingw.bat
```

For MSVC, run `build_msvc.bat` instead. Then check the included example:

```powershell
.\lloyd.exe check .\lloyd_demo.lloyd
```

The command-line interface is:

```text
lloyd check <file.lloyd>
```

Exit codes: `0` means the file was certified for the supported fragment, `1`
means a source or proof error (or an unfinished theorem), and `2` means a file
or command-line error.

## Implemented fragment

This release certifies the intuitionistic propositional fragment of Lloyd.
It supports propositional atoms, `True`, `False`, `not`, `and`, `or`, `/\\`,
`\\/`, `->`, and `<->`; axioms; both documented theorem layouts; `Step`,
`Hence`, `Todo`, `Print axioms`; and the proof rules listed below.

```text
intro h : P => proof
AndIntro proof proof
h.1                 h.2
imp_intro("h", formula("P"), proof)
imp_apply(proof, proof)
and_intro(proof, proof)     and_left(proof)      and_right(proof)
or_left(proof, formula("Q"))
or_right(formula("P"), proof)
or_cases(proof, "left", left_proof, "right", right_proof)
false_elim(proof, formula("P"))
iff_intro(proof, proof)     iff_left(proof)      iff_right(proof)
```

## Important boundary

The revised LRS-Alpha document defines a larger language than this release
implements. This version does **not** certify `Transparent`, `Notation`, definitions,
equality, natural-number arithmetic, induction/cases, quantifiers, imports,
or dependent types. In particular, the document's `add_comm` example requires
those features and is not certified by this version. Unsupported declarations
and proof syntax are rejected rather than trusted.

Identifiers use ASCII letters, digits, underscores, and qualified-name dots.
UTF-8 file input is accepted, but Unicode identifiers and NFC normalization
are not implemented yet.

# 注意

现有代码未完全实现文档规范，请自行审查规范！