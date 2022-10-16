import Lake
open Lake DSL

package tao1 {
  -- add package configuration options here
}

lean_lib Tao1 {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe tao1 {
  root := `Main
}
