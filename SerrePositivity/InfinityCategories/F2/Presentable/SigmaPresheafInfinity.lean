module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteProductPreservation
public import SerrePositivity.InfinityCategories.F1.PresheafInfinity
public import SerrePositivity.InfinityCategories.Core.FullSubcomplexFibration
public import SerrePositivity.InfinityCategories.F1B.FullSubcomplexMapping

/-!
概要：有限余積を積へ送る前層の ∞ 圏 P_Σ(C)。
方針：元の P(C) の頂点が表す反変関手の有限積保存を頂点条件に取る。
規約：有限積条件は Cᵒᵖ の元の全極限錐を使う。反射や局所化の存在は仮定しない。
使われ方：HTT 5.5.8.8、Yoneda の因子化と sifted 余極限での閉性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 前層の元の反変関手が、有限余積を積へ送る条件。 -/
def IsSigmaPresheaf {C : SSet.{u}} (F : (PresheafInfinity C) _⦋0⦌) : Prop :=
  PreservesFiniteProductsFromSmallSource ((presheafInfinityObjectEquiv C).symm F)

/-- 元の反変関手を頂点表示したとき、P_Σ の条件は元の関手の有限積保存。 -/
lemma isSigmaPresheaf_object_iff {C : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) :
    IsSigmaPresheaf (presheafInfinityObjectEquiv C F) ↔
      PreservesFiniteProductsFromSmallSource F := by
  simp only [IsSigmaPresheaf, Equiv.symm_apply_apply]

/-- 有限余積を積へ送る前層の、元の P(C) 内の全部分複体。 -/
def sigmaPresheavesSubcomplex (C : SSet.{u}) : (PresheafInfinity C).Subcomplex :=
  fullSubcomplexOnVertices (PresheafInfinity C) IsSigmaPresheaf

/-- HTT 5.5.8.8 の P_Σ(C)。有限余積を持つ C の前層の全部分 ∞ 圏。 -/
def SigmaPresheafInfinity (C : SSet.{u}) : SSet.{u + 1} := sigmaPresheavesSubcomplex C

/-- P_Σ(C) は元の前層 ∞ 圏の全部分 quasicategory。 -/
instance sigmaPresheafInfinity_quasicategory (C : SSet.{u}) :
    Quasicategory (SigmaPresheafInfinity C) :=
  inferInstanceAs (Quasicategory
    (fullSubcomplexOnVertices (PresheafInfinity C) IsSigmaPresheaf : SSet.{u + 1}))

/-- P_Σ(C) から元の前層 ∞ 圏への包含。 -/
def sigmaPresheafInfinityInclusion (C : SSet.{u}) :
    SigmaPresheafInfinity C ⟶ PresheafInfinity C := (sigmaPresheavesSubcomplex C).ι

/-- 包含は元の写像空間で充満忠実。 -/
lemma sigmaPresheafInfinityInclusion_isFullyFaithful (C : SSet.{u}) :
    IsFullyFaithful (sigmaPresheafInfinityInclusion C) :=
  isFullyFaithful_fullSubcomplexOnVertices_ι _ _

/-- P_Σ の対象は、元の前層の有限余積から積への保存条件を満たす。 -/
lemma sigmaPresheafInfinity_vertex {C : SSet.{u}}
    (F : (SigmaPresheafInfinity C) _⦋0⦌) :
    IsSigmaPresheaf ((sigmaPresheafInfinityInclusion C).app (Opposite.op ⦋0⦌) F) :=
  fullSubcomplexOnVertices_vertex F

/-- P_Σ の対象条件は元の前層 ∞ 圏での対象同型に関して不変。 -/
lemma isSigmaPresheaf_iff_of_vertexIso {C : SSet.{u}}
    {F G : (PresheafInfinity C) _⦋0⦌} (e : VertexIso F G) :
    IsSigmaPresheaf F ↔ IsSigmaPresheaf G := by
  let f := (presheafInfinityObjectEquiv C).symm F
  let g := (presheafInfinityObjectEquiv C).symm G
  have he : FunctorIso f g := by
    have hf : functorVertex f = F := (presheafInfinityObjectEquiv C).apply_symm_apply F
    have hg : functorVertex g = G := (presheafInfinityObjectEquiv C).apply_symm_apply G
    change VertexIso (functorVertex f) (functorVertex g)
    rw [hf, hg]
    exact e
  exact preservesFiniteProductsFromSmallSource_iff_of_functorIso he

/-- 全頂点が有限余積を積へ送る前層の族を、元の族ごと P_Σ へ制限する。 -/
def sigmaPresheafInfinityLift {A : SSet.{u + 1}} {C : SSet.{u}}
    (F : A ⟶ PresheafInfinity C)
    (hF : ∀ a : A _⦋0⦌, IsSigmaPresheaf (F.app (Opposite.op ⦋0⦌) a)) :
    A ⟶ SigmaPresheafInfinity C := fullSubcomplexLift IsSigmaPresheaf F hF

/-- 族の P_Σ への制限は、包含後に元の全 ∞ 関手を厳密に回収する。 -/
lemma sigmaPresheafInfinityLift_inclusion {A : SSet.{u + 1}} {C : SSet.{u}}
    (F : A ⟶ PresheafInfinity C)
    (hF : ∀ a : A _⦋0⦌, IsSigmaPresheaf (F.app (Opposite.op ⦋0⦌) a)) :
    sigmaPresheafInfinityLift F hF ≫ sigmaPresheafInfinityInclusion C = F :=
  fullSubcomplexLift_ι _ _ _

end SerrePositivity.InfinityCategories.HomotopyLimits
