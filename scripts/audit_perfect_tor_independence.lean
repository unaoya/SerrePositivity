import SerrePositivity.CommutativeAlgebra.PerfectTorIndependence
import Mathlib.Util.AssertNoSorry

assert_no_sorry SerrePositivity.tor_vanishing_of_perfect

#print axioms SerrePositivity.tor_vanishing_of_perfect

open Lean in
run_cmd do
  let axioms ← collectAxioms ``SerrePositivity.tor_vanishing_of_perfect
  for name in axioms do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains name do
      throwError "標準三公理以外への依存: {name}"
  logInfo "完全環の Tor 独立性: sorry 非依存・標準三公理のみ"

universe u
open CategoryTheory CategoryTheory.Limits

-- 指定された型全体を検査し、追加仮定がないことを固定する。
example
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p] [CharP C p]
    [PerfectRing A p] [PerfectRing B p] [PerfectRing C p] :
    ∀ i : ℕ, 0 < i →
      IsZero (((Tor (ModuleCat.{u} A) i).obj (ModuleCat.of A B)).obj (ModuleCat.of A C)) :=
  SerrePositivity.tor_vanishing_of_perfect p
