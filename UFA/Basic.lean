import Mathlib.Data.Real.Basic


structure MetricSpaceElement

structure MetricSpace (α: Type _ ) where
  dist: α -> α -> Real 


axiom DistNonneg{T: Type _}{x: MetricSpace T} {a b: T}: x.dist a b >= 0
axiom DistZero{T: Type _}{x: MetricSpace T}{a b: T}: x.dist a b = 0 <-> a = b
axiom DistSym{T: Type _}{x: MetricSpace T}{a b: T}: (x.dist a b) = (x.dist b a)
