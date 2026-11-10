module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.VertexComparison
public import SerrePositivity.InfinityCategories.Core.PointCosliceEdge
public import SerrePositivity.InfinityCategories.Core.FullSubcomplexFibration
public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitMappingAdjunction

/-!
概要：二つの presentable 圏の間の随伴を、元の関手圏の core と実単位の空間で表す。
方針：合成 LR に恒等関手の coslice を引き戻し、単位判定を満たす部分の core を取る。
規約：単位を h Fun の同型類だけに置き換えず、coslice の全高次単体を保持する。
使われ方：全 Pr 対応の二対象間の単位の空間と両射影の検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：左写像空間を元の全関手圏へ含める。
方針：core と保存条件の全部分複体の二つの包含を使う。
規約：e1 の定義の単体をそのまま使う。
使われ方：単位の終域となる左右の合成。 -/
def leftMappingInclusion (C D : PresentableInfinityObject.{u}) :
    PrLMappingSpace C D ⟶ (ihom C.obj).obj D.obj :=
  (quasicategoryCore (PrLFunctorSpace C D)).ι ≫
    (fullSubcomplexOnVertices ((ihom C.obj).obj D.obj)
      (fun v ↦ _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits ((functorVertexEquiv C.obj D.obj).symm v))).ι

/-- 概要：右写像空間を元の全関手圏へ含める。
方針：core と右保存条件の包含を合成する。
規約：accessibility と小極限保存を保持する。
使われ方：元の左右の合成の定義。 -/
def rightMappingInclusion (C D : PresentableInfinityObject.{u}) :
    PrRMappingSpace C D ⟶ (ihom C.obj).obj D.obj :=
  (quasicategoryCore (PrRFunctorSpace C D)).ι ≫
    (fullSubcomplexOnVertices ((ihom C.obj).obj D.obj)
      (fun v ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor ((functorVertexEquiv C.obj D.obj).symm v) ∧
        PreservesSmallLimits ((functorVertexEquiv C.obj D.obj).symm v))).ι

/-- 概要：左右の元の写像空間から LR の全関手圏への合成。
方針：包含の積の後に内部 Hom の豊穣合成を使う。
規約：全ての高次関手同値に作用する単体集合の射。
使われ方：実単位の coslice の底変換。 -/
def unitComposition (C D : PresentableInfinityObject.{u}) :
    PrLMappingSpace C D ⊗ PrRMappingSpace D C ⟶ (ihom C.obj).obj C.obj :=
  (leftMappingInclusion C D ⊗ₘ rightMappingInclusion D C) ≫
    MonoidalClosed.comp C.obj D.obj C.obj

/-- 概要：単位の底の合成写像の頂点は元の左右の関手の合成。
方針：関手頂点の表示の両逆を使い、元の豊穣合成を計算する。
規約：元の e1 の頂点を保持する。
使われ方：coslice の単位の終域の厳密な同定。 -/
lemma unitComposition_vertex {C D : PresentableInfinityObject.{u}}
    (v : PrLMappingSpace C D _⦋0⦌) (w : PrRMappingSpace D C _⦋0⦌) :
    (unitComposition C D).app (Opposite.op ⦋0⦌) (v, w) =
      functorVertex (leftVertexFunctor v.val ≫ rightVertexFunctor w.val) := by
  have hL : functorVertex (leftVertexFunctor v.val) = v.val.val :=
    (functorVertexEquiv C.obj D.obj).apply_symm_apply v.val.val
  have hR : functorVertex (rightVertexFunctor w.val) = w.val.val :=
    (functorVertexEquiv D.obj C.obj).apply_symm_apply w.val.val
  change (MonoidalClosed.comp C.obj D.obj C.obj).app (Opposite.op ⦋0⦌)
    (v.val.val, w.val.val) = _
  rw [← hL, ← hR]
  rfl

/-- 概要：元の左右の関手と id→LR の実単位の全空間。
方針：恒等関手の coslice の射影を合成写像で引き戻す。
規約：随伴条件を課す前の単位を全て保持する。
使われ方：随伴単位の部分空間を作る母空間。 -/
def RawAdjointUnitSpace (C D : PresentableInfinityObject.{u}) : SSet.{u + 1} :=
  pullback (sliceUnderProjection (SSet.yonedaEquiv.symm (functorVertex (𝟙 C.obj))))
    (unitComposition C D)

instance rawAdjointUnitSpace_projection_leftFibration (C D : PresentableInfinityObject.{u}) :
    LeftFibration (pullback.snd
      (sliceUnderProjection (SSet.yonedaEquiv.symm (functorVertex (𝟙 C.obj))))
      (unitComposition C D)) :=
  ⟨leftFibrations.pullback_snd _ _ (LeftFibration.mem (p :=
    sliceUnderProjection (SSet.yonedaEquiv.symm (functorVertex (𝟙 C.obj)))))⟩

instance rawAdjointUnitSpace_quasicategory (C D : PresentableInfinityObject.{u}) :
    Quasicategory (RawAdjointUnitSpace C D) := by
  letI : Quasicategory (PrLMappingSpace C D ⊗ PrRMappingSpace D C) :=
    quasicategory_of_innerFibration
      (CartesianMonoidalCategory.fst (PrLMappingSpace C D) (PrRMappingSpace D C))
  exact quasicategory_of_innerFibration (pullback.snd
    (sliceUnderProjection (SSet.yonedaEquiv.symm (functorVertex (𝟙 C.obj))))
    (unitComposition C D))

/-- 概要：実単位の空間の左関手を元の単体集合の射として読む。
方針：引き戻しの底の第一成分と二つの包含を読む。
規約：元の e1 の頂点の関手。
使われ方：単位の始域と終域の指定。 -/
def unitLeftFunctor {C D : PresentableInfinityObject.{u}}
    (x : RawAdjointUnitSpace C D _⦋0⦌) : C.obj ⟶ D.obj :=
  leftVertexFunctor (((pullback.snd _ (unitComposition C D)).app (Opposite.op ⦋0⦌) x).1.val)

/-- 概要：実単位の空間の右関手を元の単体集合の射として読む。
方針：引き戻しの底の第二成分から右関手圏の頂点を取り出す。
規約：元の始域・標的を保持する。
使われ方：随伴の右側の指定。 -/
def unitRightFunctor {C D : PresentableInfinityObject.{u}}
    (x : RawAdjointUnitSpace C D _⦋0⦌) : D.obj ⟶ C.obj :=
  rightVertexFunctor (((pullback.snd _ (unitComposition C D)).app (Opposite.op ⦋0⦌) x).2.val)

/-- 概要：実単位の coslice 頂点を id→LR の元の辺に戻す。
方針：coslice の辺の両端を引き戻しの可換性で同定する。
規約：元の一次単体を変更しない。
使われ方：実単位の随伴判定。 -/
def unitCorrespondenceEdge {C D : PresentableInfinityObject.{u}}
    (x : RawAdjointUnitSpace C D _⦋0⦌) :
    SSet.Truncated.Edge (X := (truncation 2).obj ((ihom C.obj).obj C.obj))
      (functorVertex (𝟙 C.obj)) (functorVertex (unitLeftFunctor x ≫ unitRightFunctor x)) where
  edge := (sliceUnderVertexEdge (functorVertex (𝟙 C.obj))
    ((pullback.fst _ (unitComposition C D)).app (Opposite.op ⦋0⦌) x)).edge
  src_eq := by
    exact (sliceUnderVertexEdge (functorVertex (𝟙 C.obj))
      ((pullback.fst _ (unitComposition C D)).app (Opposite.op ⦋0⦌) x)).src_eq
  tgt_eq := by
    rw [(sliceUnderVertexEdge (functorVertex (𝟙 C.obj))
      ((pullback.fst _ (unitComposition C D)).app (Opposite.op ⦋0⦌) x)).tgt_eq]
    let p := sliceUnderProjection (SSet.yonedaEquiv.symm (functorVertex (𝟙 C.obj)))
    have h := ConcreteCategory.congr_hom
      (NatTrans.congr_app (pullback.condition (f := p) (g := unitComposition C D))
        (Opposite.op ⦋0⦌)) x
    change p.app (Opposite.op ⦋0⦌)
        ((pullback.fst p (unitComposition C D)).app (Opposite.op ⦋0⦌) x) =
      (unitComposition C D).app (Opposite.op ⦋0⦌)
        ((pullback.snd p (unitComposition C D)).app (Opposite.op ⦋0⦌) x) at h
    exact h.trans (unitComposition_vertex _ _)

/-- 概要：実単位が与える h Fun の単位の表示。
方針：元の辺のホモトピー類を取る。
規約：母空間には元の単位の全高次単体が残る。
使われ方：随伴単位の頂点条件。 -/
def unitCorrespondenceHom {C D : PresentableInfinityObject.{u}}
    (x : RawAdjointUnitSpace C D _⦋0⦌) :
    FunctorHom (𝟙 C.obj) (unitLeftFunctor x ≫ unitRightFunctor x) :=
  SSet.Truncated.HomotopyCategory.homMk (unitCorrespondenceEdge x)

/-- 概要：実単位が随伴を定めることを頂点条件として課す。
方針：指定単位の写像空間判定を使用する。
規約：単位の同値類を頂点に付けるだけの離散空間にはしない。
使われ方：随伴対応の写像空間。 -/
def AdjointUnitMappingSpace (C D : PresentableInfinityObject.{u}) : SSet.{u + 1} :=
  quasicategoryCore (fullSubcomplexOnVertices (RawAdjointUnitSpace C D)
    (fun x ↦ UnitMappingSpaceCondition (unitCorrespondenceHom x)))

instance adjointUnitMappingSpace_kanComplex (C D : PresentableInfinityObject.{u}) :
    KanComplex (AdjointUnitMappingSpace C D) := by
  dsimp only [AdjointUnitMappingSpace]
  infer_instance

/-- 概要：随伴単位の写像空間から元の実単位の空間への包含。
方針：core と単位条件の全部分複体の包含を合成する。
規約：実単位と左右の関手を全次数で保持する。
使われ方：左右の射影と随伴データの回収。 -/
def adjointUnitUnderlying (C D : PresentableInfinityObject.{u}) :
    AdjointUnitMappingSpace C D ⟶ RawAdjointUnitSpace C D :=
  (quasicategoryCore (fullSubcomplexOnVertices (RawAdjointUnitSpace C D)
    (fun x ↦ UnitMappingSpaceCondition (unitCorrespondenceHom x)))).ι ≫
    (fullSubcomplexOnVertices (RawAdjointUnitSpace C D)
      (fun x ↦ UnitMappingSpaceCondition (unitCorrespondenceHom x))).ι

/-- 概要：実単位を持つ随伴の空間の左射影。
方針：元の引き戻しの底の第一成分へ送る。
規約：e1 の元の Pr^L 写像空間への単体集合の射。
使われ方：対応の左射影の写像空間の検証。 -/
def adjointUnitLeft (C D : PresentableInfinityObject.{u}) :
    AdjointUnitMappingSpace C D ⟶ PrLMappingSpace C D :=
  adjointUnitUnderlying C D ≫ pullback.snd _ (unitComposition C D) ≫
    CartesianMonoidalCategory.fst _ _

/-- 概要：実単位を持つ随伴の空間の右射影。
方針：元の引き戻しの底の第二成分へ送る。
規約：始域と標的を逆にした e1 の元の Pr^R 写像空間への単体集合の射。
使われ方：対応の右射影の写像空間の検証。 -/
def adjointUnitRight (C D : PresentableInfinityObject.{u}) :
    AdjointUnitMappingSpace C D ⟶ PrRMappingSpace D C :=
  adjointUnitUnderlying C D ≫ pullback.snd _ (unitComposition C D) ≫
    CartesianMonoidalCategory.snd _ _

/-- 概要：随伴単位の写像空間の各頂点から元の全随伴を回収する。
方針：頂点の単位条件に指定単位の随伴判定を適用する。
規約：選んだ実単位の h Fun の表示を使う。
使われ方：対応の両射影と元の随伴の照合。 -/
def adjointUnitAdjunction {C D : PresentableInfinityObject.{u}}
    (x : AdjointUnitMappingSpace C D _⦋0⦌) :
    QCatAdjunction (unitLeftFunctor x.val.val) (unitRightFunctor x.val.val) :=
  qcatAdjunctionOfUnitMappingSpaceCondition (unitCorrespondenceHom x.val.val)
    (fullSubcomplexOnVertices_vertex x.val)

/-- 概要：対応の頂点から回収した随伴は、指定した実単位を保つ。
方針：指定単位による随伴判定の回収公式を適用する。
規約：h Fun の射の等式であり、単位を選び直さない。
使われ方：対応の頂点と普遍単位の comma 模型の比較。 -/
lemma adjointUnitAdjunction_unitHom {C D : PresentableInfinityObject.{u}}
    (x : AdjointUnitMappingSpace C D _⦋0⦌) :
    (adjointUnitAdjunction x).unitHom = unitCorrespondenceHom x.val.val :=
  qcatAdjunctionOfUnitMappingSpaceCondition_unitHom _ _

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
