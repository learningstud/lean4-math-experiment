import Lake
open Lake DSL

package assistant {
  -- add package configuration options here
}

lean_lib Geometry {
  -- add library configuration options here
}

lean_lib Algebra {
  -- add library configuration options here
}

lean_lib Buzzard {
  -- add library configuration options here
}

lean_lib Landau {
  -- add library configuration options here
}

lean_lib HoTT {
  -- add library configuration options here
}

lean_lib Halmos
lean_lib ApostolCalculus

@[default_target]
lean_exe assistant {
  root := `Cmd
}
