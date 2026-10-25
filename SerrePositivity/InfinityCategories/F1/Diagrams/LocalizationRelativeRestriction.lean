module

public import SerrePositivity.InfinityCategories.F1.Diagrams.LocalizedRelativeFunctorEquivalence
public import SerrePositivity.InfinityCategories.F1.Diagrams.LocalizedRelativeFunctorFiberIso
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorPrecomposition

/-!
概要：局所化に沿う left fibration への相対関手の制限は同値。
方針：同じ底上の全空間比較の fiber 同値を、元の相対前合成と厳密に同定する。
規約：全関手空間内の同型へ弱めず、指定底の相対関手空間自身で結論する。
使われ方：単体圏の一般初頂点写像に沿う空間値全族の降下。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ底の全空間比較の fiber への作用は、元の相対前合成そのものである。 -/
lemma localizationRelativeFiberMap_eq {N A E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (f : N ⟶ A) (W : Set (N _⦋1⦌))
    (hf : InvertsEdges f W) (p : E ⟶ B) [LeftFibration p] (b : A ⟶ B) :
    vertexFiberMap ((ihom A).map p) (localizationRelativeProjection f W hf p)
      (localizationRelativeTotalMap f W hf p) (localizationRelativeTotalMap_projection f W hf p)
      (functorVertex b) ≫ (localizationRelativeFiberIso f W hf p b).hom =
        relativeFunctorPre p b f := by
  apply vertexFiber_hom_ext ((ihom N).map p) (functorVertex (f ≫ b))
  rw [Category.assoc, localizationRelativeFiberIso_hom_ι, ← Category.assoc,
    vertexFiberMap_ι, Category.assoc,
    ← Category.assoc (localizationRelativeTotalMap f W hf p),
    localizationRelativeTotalMap_restriction, localizationPrecomposition_ι, relativeFunctorPre_ι]

/-- 局所化に沿う left fibration への相対関手の制限は、指定底を保つ同値である。 -/
lemma IsLocalization.relativeFunctorPre_isQCatEquivalence {N A E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] {f : N ⟶ A} {W : Set (N _⦋1⦌)}
    (hL : IsLocalization f W) (p : E ⟶ B) [LeftFibration p] (b : A ⟶ B) :
    IsQCatEquivalence (relativeFunctorPre p b f) := by
  have h := (localizationRelativeTotalMap_fiber_isQCatEquivalence f W hL.choose p hL b).comp
    (qCatEquivalenceOfIso (localizationRelativeFiberIso f W hL.choose p b)).isQCatEquivalence
  change IsQCatEquivalence (vertexFiberMap ((ihom A).map p)
    (localizationRelativeProjection f W hL.choose p)
    (localizationRelativeTotalMap f W hL.choose p)
    (localizationRelativeTotalMap_projection f W hL.choose p) (functorVertex b) ≫
      (localizationRelativeFiberIso f W hL.choose p b).hom) at h
  rwa [localizationRelativeFiberMap_eq] at h

end SerrePositivity.InfinityCategories
