module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConvolutionFunctor
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.UnitCoalgebra
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConvolutionUnitSourceEvaluation
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConvolutionAssemblyTransport
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraIso

/-!
模型。文献の定義との比較は後で
# 単位余代数からの convolution と元の代数

概要：Berger–Fresse §3.1 の Hom(単位,B) と B の標準同型は代数の作用を保つ。
方針：Hopf 対角の右余単位則と単位始域の反復評価を組み立てに適用する。
規約：augmentation は与えた Hopf 構造の余単位を用いる。
使われ方：区間の端点・収縮の前合成から代数の評価射・定数射を得る。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

private lemma assembly_unit_core {K : Type u} [Category.{v} K] [MonoidalCategory K]
    [SymmetricCategory K] {C D V T B : K}
    (d : C ⟶ C ⊗ D) (ε : D ⟶ 𝟙_ K) (v : V ⟶ T) (a : C ⊗ T ⟶ B)
    (hd : d ≫ (C ◁ ε) ≫ (ρ_ C).hom = 𝟙 C) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly d ((ε ▷ (𝟙_ K)) ≫ (λ_ (𝟙_ K)).hom)
      ((v ▷ (𝟙_ K)) ≫ (ρ_ T).hom) a =
      (ρ_ (C ⊗ V)).hom ≫ (C ◁ v) ≫ a := by
  have hdiag : (𝟙 C) ≫ (ρ_ C).inv = d ≫ (𝟙 C ⊗ₘ ε) := by
    apply (cancel_mono (ρ_ C).hom).1
    simpa only [Category.id_comp, Category.assoc, Iso.inv_hom_id, id_tensorHom] using hd.symm
  have hn := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly_coefficient d ((ε ▷ (𝟙_ K)) ≫ (λ_ (𝟙_ K)).hom)
    ((v ▷ (𝟙_ K)) ≫ (ρ_ T).hom) a (ρ_ C).inv (λ_ (𝟙_ K)).hom a
    (𝟙 C) (𝟙 C) ε hdiag rfl
    (by simp only [id_whiskerRight, Category.id_comp])
  simp only [id_whiskerRight, Category.id_comp] at hn
  rw [← hn]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly, tensorμ, braiding_tensorUnit_left,
    comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  monoidal

private lemma assembly_unit_source {K : Type u} [Category.{v} K] [MonoidalCategory K]
    [SymmetricCategory K] {C D V W T B : K}
    (d : C ⟶ C ⊗ D) (ε : D ⟶ 𝟙_ K) (U : W ≅ 𝟙_ K) (v : V ⟶ T)
    (a : C ⊗ T ⟶ B) (hd : d ≫ (C ◁ ε) ≫ (ρ_ C).hom = 𝟙 C) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly d ((ε ▷ (𝟙_ K)) ≫ (λ_ (𝟙_ K)).hom ≫ U.inv)
      ((v ⊗ₘ U.hom) ≫ (ρ_ T).hom) a =
      (ρ_ (C ⊗ V)).hom ≫ (C ◁ v) ≫ a := by
  have hn := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly_transport d
    ((ε ▷ (𝟙_ K)) ≫ (λ_ (𝟙_ K)).hom ≫ U.inv)
    ((v ⊗ₘ U.hom) ≫ (ρ_ T).hom) a
    ((ε ▷ (𝟙_ K)) ≫ (λ_ (𝟙_ K)).hom)
    ((v ▷ (𝟙_ K)) ≫ (ρ_ T).hom) a (𝟙 V) U.hom (𝟙 T)
    (by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
    (by simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.id_comp,
      Category.comp_id])
    (by simp only [whiskerLeft_id, Category.id_comp])
  simp only [whiskerLeft_id, id_whiskerRight, Category.id_comp] at hn
  exact hn.symm.trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.assembly_unit_core d ε v a hd)

namespace Operad

variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] _root_.SerrePositivity.TensorPowers.power
attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.unitCoalgebra complexClosed complexMonoidalClosed

/-- 概要：単位余代数の convolution を評価すると元の代数の作用になる（BF §3.1）。
方針：単位始域の反復評価と Hopf 対角の右余単位則を使う。
規約：右 tensor の単位子を明示する。
使われ方：標準の単位同型が代数射であることを証明する。 -/
lemma convolutionUncurriedAction_unit_source (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) (B : P.Algebra) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionUncurriedAction hP (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.unitCoalgebra hP.counit) B n =
    (ρ_ (P.arity n ⊗ power (homComplex A (𝟙_ (Complex A)) B.carrier) n)).hom ≫
      (P.arity n ◁ _root_.SerrePositivity.TensorPowers.map
        (MonoidalClosed.unitIsoSelf (C := Complex A) (X := B.carrier)).hom n) ≫
      B.action n := by
  change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly (hP.diagonalComponent n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.unitCoaction hP.counit n)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation (𝟙_ (Complex A)) B.carrier n) (B.action n) = _
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation_unit_source]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.assembly_unit_source (hP.diagonalComponent n)
    (hP.counit.map.app (_root_.SerrePositivity.FiniteBijection.of n)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso (Complex A) n)
    (_root_.SerrePositivity.TensorPowers.map (MonoidalClosed.unitIsoSelf (C := Complex A) (X := B.carrier)).hom n)
    (B.action n) (hP.right_counit n)

/-- 概要：単位からの Hom の標準同型は convolution の全演算を保つ（BF §3.1）。
方針：右転置の単位評価に評価後の convolution の公式を適用する。
規約：標準の底の同型の順方向を使う。
使われ方：単位余代数からの convolution と元の代数を同型にする。 -/
lemma convolutionAction_unit_source (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) (B : P.Algebra) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction hP (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.unitCoalgebra hP.counit) B n ≫
      (MonoidalClosed.unitIsoSelf (C := Complex A) (X := B.carrier)).hom =
    (P.arity n ◁ _root_.SerrePositivity.TensorPowers.map
      (MonoidalClosed.unitIsoSelf (C := Complex A) (X := B.carrier)).hom n) ≫
      B.action n := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.curryRight_unit_source_evaluation,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionUncurriedAction_unit_source]
  erw [Iso.inv_hom_id_assoc]

/-- 概要：単位余代数からの convolution は元の代数に同型（BF §3.1）。
方針：全演算を保つ底の標準同型を代数の同型へ上げる。
規約：底の射は既存の MonoidalClosed.unitIsoSelf と厳密に同じ。
使われ方：区間の端点評価と定数射を元の代数へ比較する。 -/
def convolutionUnitIso (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) (B : P.Algebra) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAlgebra hP (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.unitCoalgebra hP.counit) B ≅ B :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.isoOfCarrierIso (MonoidalClosed.unitIsoSelf (C := Complex A) (X := B.carrier))
    (fun n => by
      change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction hP (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.unitCoalgebra hP.counit) B n ≫
        (MonoidalClosed.unitIsoSelf (C := Complex A) (X := B.carrier)).hom =
        (𝟙 (P.arity n) ⊗ₘ _root_.SerrePositivity.TensorPowers.map
          (MonoidalClosed.unitIsoSelf (C := Complex A) (X := B.carrier)).hom n) ≫ B.action n
      simpa only [id_tensorHom] using _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction_unit_source hP B n)

/-- 概要：単位余代数との代数同型は値域について自然（BF §3.1）。
方針：底の Hom の標準単位同型の自然性を代数射の等式へ上げる。
規約：任意の P 代数射について述べる。
使われ方：自然な端点評価・定数射を構成する。 -/
def convolutionUnitNatIso (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionFunctor hP (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.unitCoalgebra hP.counit) ≅ 𝟭 P.Algebra :=
  NatIso.ofComponents (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionUnitIso hP) (by
    intro B B' f
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext
    exact (MonoidalClosed.unitNatIso (C := Complex A)).inv.naturality f.hom)

end Operad

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
