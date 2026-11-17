module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.CompletedTotalComparisonIso
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
# 厳密な余単体的入力での完備テンソルと Tot

## 概要
加法的な関手と交代余面写像複体の指定同型を使い、標準完備比較を厳密な余単体的入力へ適用する。

## 方針
交代和の各項を元の関手で写し、同じ積全複体と比較鎖写像を使う。

## 規約
対象ごとの分解を図式へ束ねず、元の固定係数模型を使う。

## 使われ方
BS 著者版 Lemma 4.22 の鎖複体版の余単体的な表示。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicTopology HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion
open scoped Simplicial

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard

/-- 加法的な関手と交代余面写像複体は、元の各項の恒等同型で可換となる。 -/
def alternatingCofaceFunctorIso {C : Type u} [Category.{v} C] [Preadditive C]
    {D : Type u} [Category.{v} D] [Preadditive D] (F : C ⥤ D) [F.Additive] :
    alternatingCofaceMapComplex C ⋙ F.mapHomologicalComplex (.up ℕ) ≅
      (CosimplicialObject.whiskering C D).obj F ⋙ alternatingCofaceMapComplex D :=
  NatIso.ofComponents (fun X => HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (by
      intro i j hij
      change i+1=j at hij
      subst j
      simp only [Functor.comp_obj, Iso.refl_hom, alternatingCofaceMapComplex, AlternatingCofaceMapComplex.obj,
        CochainComplex.of_d, AlternatingCofaceMapComplex.objD,
        Functor.mapHomologicalComplex_obj_d, Category.id_comp, Category.comp_id,
        Functor.map_sum, Functor.map_zsmul] <;> rfl)) (by intro X Y g; apply HomologicalComplex.Hom.ext; funext n; simp)

variable {R S : Type u} [CommRing R] [CommRing S]

/-- 厳密な余単体的複体の同じ指定積全複体。 -/
abbrev cosimplicialTotal (X : CosimplicialObject (Complex R)) : Complex R :=
  total ((alternatingCofaceMapComplex (Complex R)).obj X)

namespace ScalarResolution
variable {f : R →+* S} (L : ScalarResolution f)

/-- 同じ標準比較を、各項の完備テンソルの余単体的 Tot へ渡す。 -/
def cosimplicialCompletedTensorComparison {r : ℕ} (x : Fin r → R)
    (X : CosimplicialObject (Complex R)) :
    DerivedCategory.Q.obj ((L.finiteCompletedTensorFunctor x).obj (cosimplicialTotal X)) ⟶
      DerivedCategory.Q.obj (cosimplicialTotal (X ⋙ L.finiteCompletedTensorFunctor x)) :=
  finiteCompletedTensorTotalComparison x L.complex
      ((alternatingCofaceMapComplex (Complex R)).obj X) ≫
    DerivedCategory.Q.map
      ((SerrePositivity.HomologicalAlgebra.cochainProductTotalizationFunctor (ModuleCat.{u} R)).mapIso
        ((alternatingCofaceFunctorIso (L.finiteCompletedTensorFunctor x)).app X)).hom

/-- 一様な下界と有限完全 Tor 振幅の下で、同じ余単体的比較は同型となる。 -/
theorem cosimplicialCompletedTensorComparison_isIso {r : ℕ} (x : Fin r → R) (c : ℕ)
    (hf : SerrePositivity.HasCochainCompleteTorAmplitude f x c)
    (X : CosimplicialObject (Complex R)) (b : ℤ)
    (hX : ∀ n : ℕ, ∀ i : ℤ, i < b → IsZero ((X.obj ⦋n⦌).homology i)) :
    IsIso (L.cosimplicialCompletedTensorComparison x X) := by
  haveI := L.finiteCompletedTensorTotalComparison_isIso x c hf
    ((alternatingCofaceMapComplex (Complex R)).obj X) b hX
  dsimp only [cosimplicialCompletedTensorComparison]
  infer_instance

end ScalarResolution
end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
