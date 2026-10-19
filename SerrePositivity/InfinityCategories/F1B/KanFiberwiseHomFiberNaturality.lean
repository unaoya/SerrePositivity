module

public import SerrePositivity.InfinityCategories.F1B.KanFiberwiseHomFiber
public import SerrePositivity.InfinityCategories.Core.VertexFiberMap

/-!
概要：fiber ごとの関手空間の fiber の同定は、元の図式の制限と可換。
方針：定値逆像の直積表示を底上の対象の射に関して自然にし、Hom 比較へ移す。
規約：同じ制限写像を実際の射の等式で比較する。
使われ方：普遍余錐の fiber の制限を通常の coconeRestriction と同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：定値逆像の直積表示は底上の対象の射にも自然。
方針：直積の両射影で pullback の誘導射と fiber の誘導射を計算する。
規約：元の射に充填性は仮定しない。
使われ方：fiber の関手空間の制限の同定。 -/
lemma kanConstantPullbackIso_map {C : SSet.{u}} {K L : Over C} (i : K ⟶ L)
    (c : C _⦋0⦌) (T : SSet.{u}) :
    overPullbackMap i (Over.mk (SSet.const c : T ⟶ C)) ≫
        (kanConstantPullbackIso L.hom c T).hom =
      (kanConstantPullbackIso K.hom c T).hom ≫
        (vertexFiberMap K.hom L.hom i.left i.w c ▷ T) := by
  let z := Over.mk (SSet.const c : T ⟶ C)
  have hfst : overPullbackMap i z ≫ pullback.fst (SSet.const c : T ⟶ C) L.hom =
      pullback.fst (SSet.const c : T ⟶ C) K.hom := overPullbackMap_fst i z
  have hsnd : overPullbackMap i z ≫ pullback.snd (SSet.const c : T ⟶ C) L.hom =
      pullback.snd (SSet.const c : T ⟶ C) K.hom ≫ i.left := overPullbackMap_snd i z
  change overPullbackMap i z ≫ _ = _
  apply CartesianMonoidalCategory.hom_ext
  · apply vertexFiber_hom_ext L.hom c
    simp only [Category.assoc, kanConstantPullbackIso_hom_fst_ι]
    rw [hsnd, ← Category.assoc (vertexFiberMap K.hom L.hom i.left i.w c ▷ T) _ _,
      whiskerRight_fst, Category.assoc, vertexFiberMap_ι]
    exact (congrArg (fun q ↦ q ≫ i.left)
      (kanConstantPullbackIso_hom_fst_ι K.hom c T)).symm
  · simp only [Category.assoc, kanConstantPullbackIso_hom_snd]
    rw [hfst, whiskerRight_snd, kanConstantPullbackIso_hom_snd]

/-- 概要：fiber ごとの関手の制限は底への射影と可換。
方針：一般の族の制限の射影の式を使う。
規約：底への射を厳密に保つ。
使われ方：制限を各頂点の fiber に入れる。 -/
lemma kanFiberwiseHomPre_projection {C D : SSet.{u}} {K L : Over C} (i : K ⟶ L) :
    kanFiberwiseHomPre (D := D) i ≫ kanFiberwiseHomProjection K.hom D =
      kanFiberwiseHomProjection L.hom D := rfl

/-- 概要：fiber ごとの関手の制限が各頂点の fiber に誘導する射。
方針：底への射影との可換性で fiber へ持ち上げる。
規約：元の底上の対象の射とは反対の向き。
使われ方：普遍余錐の族の制限の fiber を扱う。 -/
def kanFiberwiseHomPreFiber {C D : SSet.{u}} {K L : Over C} (i : K ⟶ L)
    (c : C _⦋0⦌) :
    vertexFiber (kanFiberwiseHomProjection L.hom D) c ⟶
      vertexFiber (kanFiberwiseHomProjection K.hom D) c :=
  vertexFiberMap _ _ (kanFiberwiseHomPre i) (kanFiberwiseHomPre_projection i) c

/-- 概要：fiber の全パラメータ Hom 比較は元の図式の制限と可換。
方針：定値逆像の直積表示の自然性と curry の制限との両立を使う。
規約：実際の fiber の制限写像を保つ。
使われ方：同型による fiber の同定の下で制限を通常の前合成として読む。 -/
lemma kanFiberwiseHomFiberHomEquiv_pre {C T D : SSet.{u}} {K L : Over C}
    (i : K ⟶ L) (c : C _⦋0⦌) (h : T ⟶ (ihom (vertexFiber L.hom c)).obj D) :
    kanFiberwiseHomFiberHomEquiv K.hom c D T
        (h ≫ (pre (vertexFiberMap K.hom L.hom i.left i.w c)).app D) =
      kanFiberwiseHomFiberHomEquiv L.hom c D T h ≫ kanFiberwiseHomPreFiber i c := by
  apply vertexFiber_hom_ext (kanFiberwiseHomProjection K.hom D) c
  rw [Category.assoc]
  change _ = kanFiberwiseHomFiberHomEquiv L.hom c D T h ≫
    vertexFiberMap _ _ (kanFiberwiseHomPre i) (kanFiberwiseHomPre_projection i) c ≫ _
  rw [vertexFiberMap_ι, ← Category.assoc, kanFiberwiseHomFiberHomEquiv_apply_ι,
    kanFiberwiseHomFiberHomEquiv_apply_ι]
  change kanFiberwiseFunctorCurry (overPullbackUnderlying K.hom)
      ⟨SSet.const c, (kanConstantPullbackIso K.hom c T).hom ≫
        uncurry (h ≫ (pre (vertexFiberMap K.hom L.hom i.left i.w c)).app D)⟩ =
    kanFiberwiseFunctorCurry (overPullbackUnderlying L.hom)
      ⟨SSet.const c, (kanConstantPullbackIso L.hom c T).hom ≫ uncurry h⟩ ≫
        kanFiberwiseFunctorPre (overPullbackMapNat i)
  rw [← kanFiberwiseFunctorCurry_pre]
  apply congrArg (fun H : pullback (SSet.const c : T ⟶ C) K.hom ⟶ D ↦
    kanFiberwiseFunctorCurry (overPullbackUnderlying K.hom)
      (⟨SSet.const c, H⟩ : KanFiberwiseFunctorSimplex (overPullbackUnderlying K.hom) D T))
  change (kanConstantPullbackIso K.hom c T).hom ≫
      uncurry (h ≫ (pre (vertexFiberMap K.hom L.hom i.left i.w c)).app D) =
    overPullbackMap i (Over.mk (SSet.const c : T ⟶ C)) ≫
      (kanConstantPullbackIso L.hom c T).hom ≫ uncurry h
  rw [uncurry_pre_app, ← Category.assoc (overPullbackMap i _) _ _,
    kanConstantPullbackIso_map, Category.assoc]

/-- 概要：fiber の比較同型の射は全パラメータの Hom 比較を表す。
方針：Yoneda の同型の射を恒等射で評価し、Hom 比較の自然性を使う。
規約：任意のパラメータ T とその射 h。
使われ方：fiber の比較同型の可換四角形の確認。 -/
lemma kanFiberwiseHomFiberIso_hom_comp {K C T D : SSet.{u}} (p : K ⟶ C)
    (c : C _⦋0⦌) (h : T ⟶ (ihom (vertexFiber p c)).obj D) :
    h ≫ (kanFiberwiseHomFiberIso p c D).hom = kanFiberwiseHomFiberHomEquiv p c D T h := by
  change h ≫ kanFiberwiseHomFiberHomEquiv p c D _ (𝟙 _) = _
  exact (kanFiberwiseHomFiberHomEquiv_naturality p c h (𝟙 _)).symm.trans
    (congrArg (kanFiberwiseHomFiberHomEquiv p c D T) (Category.comp_id h))

/-- 概要：fiber の関手圏との同定は元の図式の制限と厳密に可換。
方針：全パラメータ Hom 比較の自然性を恒等射に適用する。
規約：同じ制限写像を同型の両側で追跡する。
使われ方：普遍余錐の制限を fiber の始対象性へ移す。 -/
lemma kanFiberwiseHomFiberIso_pre {C D : SSet.{u}} {K L : Over C}
    (i : K ⟶ L) (c : C _⦋0⦌) :
    (pre (vertexFiberMap K.hom L.hom i.left i.w c)).app D ≫
        (kanFiberwiseHomFiberIso K.hom c D).hom =
      (kanFiberwiseHomFiberIso L.hom c D).hom ≫ kanFiberwiseHomPreFiber i c := by
  rw [kanFiberwiseHomFiberIso_hom_comp]
  have h := kanFiberwiseHomFiberHomEquiv_pre (D := D) i c (𝟙 _)
  rw [Category.id_comp] at h
  exact h.trans (congrArg (fun q ↦ q ≫ kanFiberwiseHomPreFiber i c)
    (kanFiberwiseHomFiberIso_hom_comp L.hom c (𝟙 _)).symm)

end SerrePositivity.InfinityCategories
