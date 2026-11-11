module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.FiberwiseHomFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap

/-!
概要：fiber ごとの関手空間の fiber の同定は、元の図式の制限と可換。
方針：定値逆像の直積表示を底上の対象の射に関して自然にし、Hom 比較へ移す。
規約：同じ制限写像を実際の射の等式で比較する。
使われ方：普遍余錐の fiber の制限を通常の coconeRestriction と同定する。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：定値逆像の直積表示は底上の対象の射にも自然。
方針：直積の両射影で pullback の誘導射と fiber の誘導射を計算する。
規約：元の射に充填性は仮定しない。
使われ方：fiber の関手空間の制限の同定。 -/
lemma constantPullbackIso_map {C : SSet.{u}} {K L : Over C} (i : K ⟶ L)
    (c : C _⦋0⦌) (T : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap i (Over.mk (SSet.const c : T ⟶ C)) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.constantPullbackIso L.hom c T).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.constantPullbackIso K.hom c T).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap K.hom L.hom i.left i.w c ▷ T) := by
  let z := Over.mk (SSet.const c : T ⟶ C)
  have hfst : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap i z ≫ pullback.fst (SSet.const c : T ⟶ C) L.hom =
      pullback.fst (SSet.const c : T ⟶ C) K.hom := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap_fst i z
  have hsnd : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap i z ≫ pullback.snd (SSet.const c : T ⟶ C) L.hom =
      pullback.snd (SSet.const c : T ⟶ C) K.hom ≫ i.left := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap_snd i z
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap i z ≫ _ = _
  apply CartesianMonoidalCategory.hom_ext
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext L.hom c
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.constantPullbackIso_hom_fst_ι]
    rw [hsnd, ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap K.hom L.hom i.left i.w c ▷ T) _ _,
      whiskerRight_fst, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι]
    exact (congrArg (fun q ↦ q ≫ i.left)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.constantPullbackIso_hom_fst_ι K.hom c T)).symm
  · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.constantPullbackIso_hom_snd]
    rw [hfst, whiskerRight_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.constantPullbackIso_hom_snd]

/-- 概要：fiber ごとの関手の制限は底への射影と可換。
方針：一般の族の制限の射影の式を使う。
規約：底への射を厳密に保つ。
使われ方：制限を各頂点の fiber に入れる。 -/
lemma fiberwiseHomPre_projection {C D : SSet.{u}} {K L : Over C} (i : K ⟶ L) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomPre (D := D) i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection K.hom D =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection L.hom D := rfl

/-- 概要：fiber ごとの関手の制限が各頂点の fiber に誘導する射。
方針：底への射影との可換性で fiber へ持ち上げる。
規約：元の底上の対象の射とは反対の向き。
使われ方：普遍余錐の族の制限の fiber を扱う。 -/
def fiberwiseHomPreFiber {C D : SSet.{u}} {K L : Over C} (i : K ⟶ L)
    (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection L.hom D) c ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection K.hom D) c :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomPre i) (fiberwiseHomPre_projection i) c

/-- 概要：fiber の全パラメータ Hom 比較は元の図式の制限と可換。
方針：定値逆像の直積表示の自然性と curry の制限との両立を使う。
規約：実際の fiber の制限写像を保つ。
使われ方：同型による fiber の同定の下で制限を通常の前合成として読む。 -/
lemma fiberwiseHomFiberHomEquiv_pre {C T D : SSet.{u}} {K L : Over C}
    (i : K ⟶ L) (c : C _⦋0⦌) (h : T ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber L.hom c)).obj D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.fiberwiseHomFiberHomEquiv K.hom c D T
        (h ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap K.hom L.hom i.left i.w c)).app D) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.fiberwiseHomFiberHomEquiv L.hom c D T h ≫ fiberwiseHomPreFiber i c := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection K.hom D) c
  rw [Category.assoc]
  change _ = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.fiberwiseHomFiberHomEquiv L.hom c D T h ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomPre i) (fiberwiseHomPre_projection i) c ≫ _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.fiberwiseHomFiberHomEquiv_apply_ι,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.fiberwiseHomFiberHomEquiv_apply_ι]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying K.hom)
      ⟨SSet.const c, (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.constantPullbackIso K.hom c T).hom ≫
        uncurry (h ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap K.hom L.hom i.left i.w c)).app D)⟩ =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying L.hom)
      ⟨SSet.const c, (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.constantPullbackIso L.hom c T).hom ≫ uncurry h⟩ ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseFunctorPre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMapNat i)
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseFunctorCurry_pre]
  apply congrArg (fun H : pullback (SSet.const c : T ⟶ C) K.hom ⟶ D ↦
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying K.hom)
      (⟨SSet.const c, H⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FiberwiseFunctorSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying K.hom) D T))
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.constantPullbackIso K.hom c T).hom ≫
      uncurry (h ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap K.hom L.hom i.left i.w c)).app D) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap i (Over.mk (SSet.const c : T ⟶ C)) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.constantPullbackIso L.hom c T).hom ≫ uncurry h
  rw [uncurry_pre_app, ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap i _) _ _,
    constantPullbackIso_map, Category.assoc]

/-- 概要：fiber の比較同型の射は全パラメータの Hom 比較を表す。
方針：Yoneda の同型の射を恒等射で評価し、Hom 比較の自然性を使う。
規約：任意のパラメータ T とその射 h。
使われ方：fiber の比較同型の可換四角形の確認。 -/
lemma fiberwiseHomFiberIso_hom_comp {K C T D : SSet.{u}} (p : K ⟶ C)
    (c : C _⦋0⦌) (h : T ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c)).obj D) :
    h ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.fiberwiseHomFiberIso p c D).hom = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.fiberwiseHomFiberHomEquiv p c D T h := by
  change h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.fiberwiseHomFiberHomEquiv p c D _ (𝟙 _) = _
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.fiberwiseHomFiberHomEquiv_naturality p c h (𝟙 _)).symm.trans
    (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.fiberwiseHomFiberHomEquiv p c D T) (Category.comp_id h))

/-- 概要：fiber の関手圏との同定は元の図式の制限と厳密に可換。
方針：全パラメータ Hom 比較の自然性を恒等射に適用する。
規約：同じ制限写像を同型の両側で追跡する。
使われ方：普遍余錐の制限を fiber の始対象性へ移す。 -/
lemma fiberwiseHomFiberIso_pre {C D : SSet.{u}} {K L : Over C}
    (i : K ⟶ L) (c : C _⦋0⦌) :
    (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap K.hom L.hom i.left i.w c)).app D ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.fiberwiseHomFiberIso K.hom c D).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.fiberwiseHomFiberIso L.hom c D).hom ≫ fiberwiseHomPreFiber i c := by
  rw [fiberwiseHomFiberIso_hom_comp]
  have h := fiberwiseHomFiberHomEquiv_pre (D := D) i c (𝟙 _)
  rw [Category.id_comp] at h
  exact h.trans (congrArg (fun q ↦ q ≫ fiberwiseHomPreFiber i c)
    (fiberwiseHomFiberIso_hom_comp L.hom c (𝟙 _)).symm)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
