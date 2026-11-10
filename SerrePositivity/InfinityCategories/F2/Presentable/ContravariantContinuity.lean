module

public import SerrePositivity.InfinityCategories.F2.Presentable.PresheafRepresentation
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
public import SerrePositivity.InfinityCategories.Core.CatInfinity.ConeValEquality

/-!
概要：小余極限を小極限へ送る空間値前層と元の全 Hom による表現可能性を定義する。
方針：元の全余錐を反転して保存性を述べ、指定した宇宙変更で表現同型を比較する。
規約：空間値は u、元の圏と前層の始域は u+1。
使われ方：随伴関手定理に必要な連続前層の表現可能性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits Ind

/-- 概要：小さい空間値前層が元の全小余極限を全極限へ送ること。
方針：指定全余錐を反転し、その F による像の極限性を量化する。
規約：添字の quasicategory 性を追加せず、全ての小さい形状を扱う。
使われ方：連続前層の表現可能性定理の仮定。 -/
def SendsSmallColimitsToLimits {C : SSet.{u + 1}} (F : C.op ⟶ SpaceInfinity.{u}) : Prop :=
  ∀ (K : SSet.{u}) (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C)
    (c : JoinCocone D), IsColimitCone c →
      IsLimitCone (mapJoinCone F (F1B.coconeReverseCone c))

/-- 概要：小さい空間値前層が元の圏の対象で全自然に表現されること。
方針：指定宇宙変更後の F と元の全表現可能 Hom の関手同型を要求する。
規約：対象ごとの Hom 集合の全単射や任意の同値族では代用しない。
使われ方：一般の presentable 圏の表現可能性の公開命題。 -/
def IsRepresentableSmallSpaceFunctor {C : SSet.{u + 1}} [Quasicategory C]
    (F : C.op ⟶ SpaceInfinity.{u}) : Prop :=
  ∃ x : C _⦋0⦌, Nonempty (FunctorIso (representablePresheafInfinity x)
    ((SSet.uliftFunctor.{u + 2, u + 1}).map F ≫ Compact.spaceUniverseDiagram))

/-- 概要：前層圏上の小余極限を小極限へ送る小さい空間値関手は表現可能。
方針：元の密度余錐へ保存性を適用し、構成済みの具体的表現同型を使う。
規約：表現対象は元の Yoneda 制限から構成し、存在入力を残さない。
使われ方：反映された presentable 圏への表現可能性の移送。 -/
lemma presheaf_isRepresentable_of_sendsSmallColimitsToLimits
    {A : SSet.{u}} [Quasicategory A] (F : (PresheafInfinity A).op ⟶ SpaceInfinity.{u})
    (hF : SendsSmallColimitsToLimits F) : IsRepresentableSmallSpaceFunctor F :=
  ⟨functorVertex (presheafRepresentationCandidate F), ⟨presheafRepresentationIso F
    (fun P ↦ hF _ _ _ (presheafDensityCocone_isColimit P))⟩⟩

/-- 概要：前層の連続性は全関手同型に沿って移る。
方針：同じ全錐の像を指定自然同型で比較する。
規約：小さい添字と元の全余錐を保持する。
使われ方：同値模型と反映模型による表現可能性の移送。 -/
lemma SendsSmallColimitsToLimits.of_functorIso {C : SSet.{u + 1}}
    {F G : C.op ⟶ SpaceInfinity.{u}} (hF : SendsSmallColimitsToLimits F)
    (e : FunctorIso F G) : SendsSmallColimitsToLimits G := by
  intro K D c hc
  exact (hF K D c hc).of_functorIso (e.precomp (F1B.coconeReverseCone c).val)

/-- 概要：連続な前層を余極限保存関手の反対に沿って制限すると連続。
方針：元の全余錐の像を反転し、同じ全錐の射の合成を照合する。
規約：指定された元の関手と余錐を保持する。
使われ方：前層反映による一般の presentable 圏の表現可能性。 -/
lemma SendsSmallColimitsToLimits.precomp_op {C D : SSet.{u + 1}}
    {F : D.op ⟶ SpaceInfinity.{u}} (hF : SendsSmallColimitsToLimits F)
    (L : C ⟶ D) (hL : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits L) :
    SendsSmallColimitsToLimits (SSet.opFunctor.map L ≫ F) := by
  intro K a c hc
  apply (F2.isLimitCone_iff_of_cone_val_eq
    (mapJoinCone F (F1B.coconeReverseCone (mapJoinCocone L c))) _ ?_).mp
      (hF K (a ≫ L) (mapJoinCocone L c) (hL K a c hc))
  simp only [mapJoinCone, F1B.coconeReverseCone_val, mapJoinCocone,
    CategoryTheory.Functor.map_comp, Category.assoc]

end SerrePositivity.InfinityCategories.F2.Presentable
