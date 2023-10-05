import Lake
open Lake DSL

package «lab1» {
  -- add package configuration options here
}

lean_lib «Lab1» {
  -- add library configuration options here
}

@[default_target]
lean_exe «lab1» {
  root := `Main
}
