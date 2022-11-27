import Lake
open Lake DSL

package geometry {
  -- add package configuration options here
}

lean_lib Geometry {
  -- add library configuration options here
}

@[default_target]
lean_exe geometry {
  root := `Main
}
