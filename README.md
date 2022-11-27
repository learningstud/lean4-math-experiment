# Hartshorne 2000 - Geometry: Euclid and Beyond

## Setup

Install elan:
```sh
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
2
leanprover/lean4:nightly
y
1
```
Screenshot:
```
Current installation options:

     default toolchain: stable
  modify PATH variable: yes

1) Proceed with installation (default)
2) Customize installation
3) Cancel installation
2

I'm going to ask you the value of each these installation options.
You may simply press the Enter key to leave unchanged.

Default toolchain? (stable/nightly/none)
leanprover/lean4:nightly

Modify PATH variable? (y/n)
y


Current installation options:

     default toolchain: leanprover/lean4:nightly
  modify PATH variable: yes

1) Proceed with installation (default)
2) Customize installation
3) Cancel installation
1
```
In the project directory:
```sh
lake init geometry
lake exe geometry
```