module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.VertexComparison

/-!
概要：随伴の頂点選択と恒等・二項合成を元の関手同型で比較する。
方針：元の随伴を合成し、同じ左随伴または右随伴に対する一意性を適用する。
規約：比較の高次の結合整合性は別工程であり、厳密な関手性を主張しない。
使われ方：Pr の双対対応の単位・合成比較の端点を固定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：元の左関手圏の恒等頂点。
方針：恒等随伴の小余極限保存を用いる。
規約：元の恒等関手の頂点を保持する。
使われ方：右随伴選択の単位比較。 -/
def leftIdentityVertex (C : PresentableInfinityObject.{u}) : PrLFunctorSpace C C _⦋0⦌ :=
  leftFunctorVertex (𝟙 C.obj) (adjunction_preservesSmallColimits (QCatAdjunction.refl C.obj))

/-- 概要：元の右関手圏の恒等頂点。
方針：恒等関手の accessibility と恒等随伴の小極限保存を用いる。
規約：同じ恒等関手を使う。
使われ方：左随伴選択の単位比較。 -/
def rightIdentityVertex (C : PresentableInfinityObject.{u}) : PrRFunctorSpace C C _⦋0⦌ :=
  rightFunctorVertex (𝟙 C.obj)
    ⟨isAccessibleFunctor_id C.obj, adjunction_preservesSmallLimits (QCatAdjunction.refl C.obj)⟩

/-- 概要：恒等左関手の選んだ右随伴は元の恒等関手と同型。
方針：恒等随伴との右随伴の一意性。
規約：h Fun 内の同型を返す。
使われ方：右随伴対応の単位比較。 -/
def chosenRightIdentityIso (C : PresentableInfinityObject.{u}) :
    FunctorIso (chosenRightAdjoint (leftIdentityVertex C)) (𝟙 C.obj) := by
  have a : QCatAdjunction (𝟙 C.obj) (chosenRightAdjoint (leftIdentityVertex C)) := by
    simpa only [leftIdentityVertex, leftFunctorVertex, leftVertexFunctor,
      Equiv.symm_apply_apply] using chosenRightAdjunction (leftIdentityVertex C)
  exact a.rightAdjointFunctorIso (QCatAdjunction.refl C.obj)

/-- 概要：恒等右関手の選んだ左随伴は元の恒等関手と同型。
方針：恒等随伴との左随伴の一意性。
規約：元の恒等関手を終端とする。
使われ方：左随伴対応の単位比較。 -/
def chosenLeftIdentityIso (C : PresentableInfinityObject.{u}) :
    FunctorIso (chosenLeftAdjoint (rightIdentityVertex C)) (𝟙 C.obj) := by
  have a : QCatAdjunction (chosenLeftAdjoint (rightIdentityVertex C)) (𝟙 C.obj) := by
    simpa only [rightIdentityVertex, rightFunctorVertex, rightVertexFunctor,
      Equiv.symm_apply_apply] using chosenLeftAdjunction (rightIdentityVertex C)
  exact a.leftAdjointFunctorIso (QCatAdjunction.refl C.obj)

/-- 概要：二つの元の左関手の合成の頂点。
方針：選んだ二つの随伴を合成して保存性を得る。
規約：合成される関手自体を変更しない。
使われ方：右随伴の合成順序反転の比較。 -/
def leftCompositeVertex {C D E : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrLFunctorSpace D E _⦋0⦌) :
    PrLFunctorSpace C E _⦋0⦌ :=
  leftFunctorVertex (leftVertexFunctor v ≫ leftVertexFunctor w)
    (adjunction_preservesSmallColimits ((chosenRightAdjunction v).comp (chosenRightAdjunction w)))

/-- 概要：左関手の合成の選んだ右随伴は逆順の右随伴の合成と同型。
方針：同じ左合成に対する右随伴の一意性。
規約：v の後に w を合成した右側は Rw の後に Rv。
使われ方：右随伴対応の二項合成比較。 -/
def chosenRightCompositeIso {C D E : PresentableInfinityObject.{u}}
    (v : PrLFunctorSpace C D _⦋0⦌) (w : PrLFunctorSpace D E _⦋0⦌) :
    FunctorIso (chosenRightAdjoint (leftCompositeVertex v w))
      (chosenRightAdjoint w ≫ chosenRightAdjoint v) := by
  have a : QCatAdjunction (leftVertexFunctor v ≫ leftVertexFunctor w)
      (chosenRightAdjoint (leftCompositeVertex v w)) := by
    simpa only [leftCompositeVertex, leftFunctorVertex, leftVertexFunctor,
      Equiv.symm_apply_apply] using chosenRightAdjunction (leftCompositeVertex v w)
  exact a.rightAdjointFunctorIso ((chosenRightAdjunction v).comp (chosenRightAdjunction w))

/-- 概要：二つの元の右関手の合成の頂点。
方針：逆順に合成した左随伴に対し d の必要方向で保存条件を回収する。
規約：元の右関手の合成を保持する。
使われ方：左随伴の合成順序反転の比較。 -/
def rightCompositeVertex {C D E : PresentableInfinityObject.{u}}
    (v : PrRFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D E _⦋0⦌) :
    PrRFunctorSpace C E _⦋0⦌ :=
  rightFunctorVertex (rightVertexFunctor v ≫ rightVertexFunctor w)
    ((exists_leftAdjoint_iff_accessible_preservesLimits E.isPresentable C.isPresentable _).mp
      ⟨_, ⟨(chosenLeftAdjunction w).comp (chosenLeftAdjunction v)⟩⟩)

/-- 概要：右関手の合成の選んだ左随伴は逆順の左随伴の合成と同型。
方針：同じ右合成に対する左随伴の一意性。
規約：元の右関手の合成と元の選択を保持する。
使われ方：左随伴対応の二項合成比較。 -/
def chosenLeftCompositeIso {C D E : PresentableInfinityObject.{u}}
    (v : PrRFunctorSpace C D _⦋0⦌) (w : PrRFunctorSpace D E _⦋0⦌) :
    FunctorIso (chosenLeftAdjoint (rightCompositeVertex v w))
      (chosenLeftAdjoint w ≫ chosenLeftAdjoint v) := by
  have a : QCatAdjunction (chosenLeftAdjoint (rightCompositeVertex v w))
      (rightVertexFunctor v ≫ rightVertexFunctor w) := by
    simpa only [rightCompositeVertex, rightFunctorVertex, rightVertexFunctor,
      Equiv.symm_apply_apply] using chosenLeftAdjunction (rightCompositeVertex v w)
  exact a.leftAdjointFunctorIso ((chosenLeftAdjunction w).comp (chosenLeftAdjunction v))

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
