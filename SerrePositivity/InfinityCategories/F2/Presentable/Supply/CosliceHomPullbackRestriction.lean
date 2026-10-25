module

public import SerrePositivity.InfinityCategories.F2.Presentable.Supply.CosliceHomRestriction
public import SerrePositivity.InfinityCategories.F2.Presentable.Supply.LeftClassificationBaseChangeHom
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorBaseChangeNaturality
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorPullbackRestriction
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorVertices

/-!
概要：coslice の実 Hom 制限を、底変換後の元の left fibration 間の Hom の同値として表示する。
方針：実底変換と実前合成を合成し、元の底上の coslice 制限との厳密な一致で判定する。
規約：同じ cosliceComparisonOver と元の引き戻しを使う。
使われ方：P-12 の指定分類 Hom の正方形と全単射性の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

local instance {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) :
    LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

/-- 概要：底上の実前合成は通常の相対前合成と元の図式等式での輸送の合成。
方針：元の fiber の包含後に射を比較する。
規約：底上の射を選び直さない。使われ方：始対象を保つ実前合成の同値性。 -/
lemma relativeOverPre_eq_pre_transport {E B : SSet.{u}} (p : E ⟶ B)
    {a b : Over B} (f : a ⟶ b) :
    relativeFunctorOverPre p f = relativeFunctorPre p b.hom f.left ≫
      eqToHom (congrArg (relativeFunctorSpace p) f.w) := by
  apply vertexFiber_hom_ext ((ihom a.left).map p) (functorVertex a.hom)
  rw [Category.assoc]
  change relativeFunctorOverPre p f ≫ _ = relativeFunctorPre p b.hom f.left ≫
    (eqToHom (congrArg (vertexFiber ((ihom a.left).map p)) (congrArg functorVertex f.w)) ≫ _)
  rw [vertexFiberTransport_ι, relativeFunctorPre_ι, relativeFunctorOverPre_ι]
  exact congrArg functorVertex f.w

/-- 概要：始対象を保つ底上の実前合成は全相対 Hom の同値。
方針：通常の相対前合成の始対象判定と図式の等式による同型を合成する。
規約：底のみ quasicategory。使われ方：coslice 作用を底上の射として使う場合の同値性。 -/
lemma relativeOverPre_isQCatEquivalence_of_initialVertices
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
    {a b : Over B} (f : a ⟶ b) (v : a.left _⦋0⦌) (hv : IsInitialVertex v)
    (hi : IsInitialVertex (f.left.app (Opposite.op ⦋0⦌) v)) :
    IsQCatEquivalence (relativeFunctorOverPre p f) := by
  rw [relativeOverPre_eq_pre_transport]
  exact (relativeHomRestriction_isQCatEquivalence_of_initialVertices p b.hom f.left v hv hi).comp
    (qCatEquivalenceOfIso (eqToIso (congrArg (relativeFunctorSpace p) f.w))).isQCatEquivalence

/-- 概要：実底変換後に元の coslice 比較で制限する全相対 Hom の射。
方針：元の豊穣底変換と、同じ cosliceComparisonOver での実前合成を合成する。
規約：底の関手は任意。使われ方：分類後の指定 Hom 比較の実空間模型。 -/
def cosliceHomPullbackRestriction {A C E : SSet.{u}}
    (F : A ⟶ C) (a : A _⦋0⦌) (p : E ⟶ C) :
    relativeFunctorSpace p (sliceUnderProjection (SSet.yonedaEquiv.symm a ≫ F)) ⟶
      relativeFunctorSpace (pullback.snd p F) (sliceUnderProjection (SSet.yonedaEquiv.symm a)) :=
  relativeFunctorPullback (sliceUnderProjection (SSet.yonedaEquiv.symm a ≫ F)) p F ≫
    relativeFunctorOverPre (pullback.snd p F)
      (Over.homMk (U := Over.mk (sliceUnderProjection (SSet.yonedaEquiv.symm a)))
        (V := Over.mk (pullback.snd (sliceUnderProjection (SSet.yonedaEquiv.symm a ≫ F)) F))
        (cosliceComparisonOver F a) (cosliceComparisonOver_projection F a))

/-- 概要：実底変換後の coslice 制限は元の底上の射の頂点を同じ実合成の頂点へ送る。
方針：元の相対 Hom の底変換と前合成の頂点の式を順に使う。
規約：引き戻し比較を選び直さない。使われ方：分類 Hom の指定正方形との零次の照合。 -/
lemma cosliceHomPullbackRestriction_vertex {A C E : SSet.{u}}
    (F : A ⟶ C) (a : A _⦋0⦌) (p : E ⟶ C)
    (f : sliceUnder (SSet.yonedaEquiv.symm a ≫ F) ⟶ E)
    (hf : f ≫ p = sliceUnderProjection (SSet.yonedaEquiv.symm a ≫ F)) :
    (cosliceHomPullbackRestriction F a p).app (Opposite.op ⦋0⦌)
      (relativeFunctorVertex p (sliceUnderProjection (SSet.yonedaEquiv.symm a ≫ F)) f hf) =
    relativeFunctorVertex (pullback.snd p F) (sliceUnderProjection (SSet.yonedaEquiv.symm a))
      (cosliceComparisonOver F a ≫
        fiberComparisonBaseChange (sliceUnderProjection (SSet.yonedaEquiv.symm a ≫ F)) p f hf F)
      (by rw [Category.assoc, fiberComparisonBaseChange_projection,
        cosliceComparisonOver_projection]) := by
  simp only [cosliceHomPullbackRestriction, NatTrans.comp_app, ConcreteCategory.comp_apply,
    relativeFunctorPullback_vertex, relativeFunctorOverPre_vertex]
  rfl

/-- 概要：実底変換後の coslice 制限は元の底上の coslice 作用による制限と厳密に一致する。
方針：底変換の前合成自然性、元の始域制限則、元の coslice 比較の射影式を使う。
規約：既存の底変換同型の順方向そのものを使う。
使われ方：実相対 Hom 比較の同値性を元の始対象で判定する。 -/
lemma cosliceHomPullbackRestriction_sourceRestriction {A C E : SSet.{u}}
    (F : A ⟶ C) (a : A _⦋0⦌) (p : E ⟶ C) :
    cosliceHomPullbackRestriction F a p ≫
      (relativeFunctorBaseChangeIso p F (sliceUnderProjection (SSet.yonedaEquiv.symm a))).hom =
    relativeFunctorOverPre p
      (Over.homMk (U := Over.mk (sliceUnderProjection (SSet.yonedaEquiv.symm a) ≫ F))
        (V := Over.mk (sliceUnderProjection (SSet.yonedaEquiv.symm a ≫ F)))
        (sliceUnderPostcomp (SSet.yonedaEquiv.symm a) F)
        (sliceUnderPostcomp_projection _ _)) := by
  let s := sliceUnderProjection (SSet.yonedaEquiv.symm a ≫ F)
  let t := sliceUnderProjection (SSet.yonedaEquiv.symm a)
  let v : Over.mk t ⟶ Over.mk (pullback.snd s F) :=
    Over.homMk (cosliceComparisonOver F a) (cosliceComparisonOver_projection F a)
  have hv : (Over.map F).map v ≫ relativeFunctorPullbackSourceMap s F =
      Over.homMk (U := Over.mk (t ≫ F)) (V := Over.mk s)
        (sliceUnderPostcomp (SSet.yonedaEquiv.symm a) F)
        (sliceUnderPostcomp_projection _ _) := by
    apply Over.OverMorphism.ext
    exact cosliceComparisonOver_postcomp F a
  change (relativeFunctorPullback s p F ≫ relativeFunctorOverPre (pullback.snd p F) v) ≫
    relativeFunctorBaseChangeForward p F t = _
  rw [Category.assoc]
  calc
    _ = relativeFunctorPullback s p F ≫
        (relativeFunctorBaseChangeForward p F (pullback.snd s F) ≫
          relativeFunctorOverPre p ((Over.map F).map v)) :=
      congrArg (fun z ↦ relativeFunctorPullback s p F ≫ z)
        (relativeFunctorBaseChangeForward_overPre p F v)
    _ = (relativeFunctorPullback s p F ≫
        (relativeFunctorBaseChangeIso p F (pullback.snd s F)).hom) ≫
          relativeFunctorOverPre p ((Over.map F).map v) := (Category.assoc _ _ _).symm
    _ = relativeFunctorOverPre p (relativeFunctorPullbackSourceMap s F) ≫
        relativeFunctorOverPre p ((Over.map F).map v) :=
      congrArg (fun z ↦ z ≫ relativeFunctorOverPre p ((Over.map F).map v))
        (relativeFunctorPullback_sourceRestriction s p F)
    _ = relativeFunctorOverPre p ((Over.map F).map v ≫ relativeFunctorPullbackSourceMap s F) :=
      (relativeFunctorOverPre_comp p _ _).symm
    _ = _ := congrArg (relativeFunctorOverPre p) hv

/-- 概要：底変換後の元の coslice 制限の実全相対 Hom 射は同値。
方針：元の底上の始対象を保つ制限の同値性を、厳密な底変換同型で反映する。
規約：元の任意の関手 F と元の left fibration を使う。
使われ方：指定された分類 Hom の制限の全単射性の実空間での証明。 -/
lemma cosliceHomPullbackRestriction_isQCatEquivalence
    {A C E : SSet.{u}} [Quasicategory A] [Quasicategory C]
    (F : A ⟶ C) (a : A _⦋0⦌) (p : E ⟶ C) [LeftFibration p] :
    IsQCatEquivalence (cosliceHomPullbackRestriction F a p) := by
  apply (qCatEquivalenceOfIso (relativeFunctorBaseChangeIso p F
    (sliceUnderProjection (SSet.yonedaEquiv.symm a)))).isQCatEquivalence.cancel_right
  change IsQCatEquivalence (cosliceHomPullbackRestriction F a p ≫
    (relativeFunctorBaseChangeIso p F (sliceUnderProjection (SSet.yonedaEquiv.symm a))).hom)
  rw [cosliceHomPullbackRestriction_sourceRestriction]
  exact relativeOverPre_isQCatEquivalence_of_initialVertices p _ (cosliceIdentityCone a)
    (cosliceIdentityCone_isInitialVertex a) (coslicePostcomp_identity_isInitial F a)

end SerrePositivity.InfinityCategories.F2.Presentable
