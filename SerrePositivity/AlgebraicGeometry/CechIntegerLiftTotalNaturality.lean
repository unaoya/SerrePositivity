module

public import SerrePositivity.AlgebraicGeometry.CechIntegerLiftTotal
public import Mathlib.Algebra.Homology.QuasiIso

/-!
概要：元の全複体の整数係数の比較を、同じ二重複体の射に自然にする。
方針：元の各直和入射で自然性を確認し、同じ標準同型へまとめる。
規約：係数の宇宙と元の直和の選択を保つ。
使われ方：元の二重Čechの射の擬同型性を既存HAのAPIへ渡す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
local notation "up" => ComplexShape.up ℕ
variable {K L : HomologicalComplex₂ (ModuleCat.{u} ℤ) up up}
variable [K.HasTotal up] [L.HasTotal up]
variable [(cechIntegerLiftBicomplex K).HasTotal up] [(cechIntegerLiftBicomplex L).HasTotal up]

/-- 同じ既存の係数関手を、元の二重複体の射に適用する。 -/
abbrev cechIntegerLiftBicomplexMap (f : K ⟶ L) :
    cechIntegerLiftBicomplex K ⟶ cechIntegerLiftBicomplex L :=
  ((cechIntegerLiftFunctor.mapHomologicalComplex up).mapHomologicalComplex up).map f

set_option backward.isDefEq.respectTransparency false in
/-- 各直和の標準比較は、元の同じ射の各次数に自然。 -/
theorem cechIntegerLiftTotalComponentIso_naturality (f : K ⟶ L) (n : ℕ) :
    (cechIntegerLiftTotalComponentIso K n).hom ≫
        cechIntegerLiftFunctor.map ((HomologicalComplex₂.total.map f up).f n) =
      (HomologicalComplex₂.total.map (cechIntegerLiftBicomplexMap f) up).f n ≫
        (cechIntegerLiftTotalComponentIso L n).hom := by
  apply HomologicalComplex₂.total.hom_ext
  intro a b h
  rw [← Category.assoc, cechIntegerLiftTotalComponentIso_ι,
    ← Functor.map_comp, HomologicalComplex₂.ιTotal_map, Functor.map_comp,
    ← Category.assoc, HomologicalComplex₂.ιTotal_map, Category.assoc,
    cechIntegerLiftTotalComponentIso_ι]
  rfl

/-- 同じ全複体の標準比較は、元の二重複体の射に自然。 -/
theorem cechIntegerLiftTotalIso_naturality (f : K ⟶ L) :
    (cechIntegerLiftTotalIso K).hom ≫
        (cechIntegerLiftFunctor.mapHomologicalComplex up).map (HomologicalComplex₂.total.map f up) =
      HomologicalComplex₂.total.map (cechIntegerLiftBicomplexMap f) up ≫
        (cechIntegerLiftTotalIso L).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact cechIntegerLiftTotalComponentIso_naturality f n

set_option backward.isDefEq.respectTransparency false in
/-- 同じ係数移送は、元の全複体の射の擬同型性を保ち反映する。 -/
theorem cechIntegerLiftTotal_quasiIso_iff (f : K ⟶ L) :
    QuasiIso (HomologicalComplex₂.total.map (cechIntegerLiftBicomplexMap f) up) ↔
      QuasiIso (HomologicalComplex₂.total.map f up) := by
  let e : Arrow.mk (HomologicalComplex₂.total.map (cechIntegerLiftBicomplexMap f) up) ≅
      Arrow.mk ((cechIntegerLiftFunctor.mapHomologicalComplex up).map
        (HomologicalComplex₂.total.map f up)) :=
    Arrow.isoMk (cechIntegerLiftTotalIso K) (cechIntegerLiftTotalIso L)
      (by exact cechIntegerLiftTotalIso_naturality f)
  exact (_root_.quasiIso_iff_of_arrow_mk_iso _ _ e).trans
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
      (HomologicalComplex₂.total.map f up) cechIntegerLiftFunctor)

end SerrePositivity.AlgebraicGeometry
