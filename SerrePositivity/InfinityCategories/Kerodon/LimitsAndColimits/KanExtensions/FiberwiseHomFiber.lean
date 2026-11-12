module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ConstantPullback

/-!
概要：fiber ごとの関手の全空間の頂点 fiber を通常の関手単体集合と同定する。
方針：任意のパラメータからの射を、定値逆像上の図式と直積の随伴を通じて比較する。
規約：fiber の厳密な同型であり、対象の対応や π₀ の対応だけではない。
使われ方：Kerodon Lemma 7.3.4.5（Tag 02ZR） の fiber ごとの普遍余錐性の移送。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：頂点上で定値な射と、その頂点 fiber への射の全単射。
方針：fiber の持ち上げと包含を往復させる。
規約：パラメータは任意。
使われ方：関手の族の底の固定条件を fiber への射にする。 -/
def vertexFiberHomEquiv {E B : SSet.{u}} (q : E ⟶ B) (c : B _⦋0⦌) (T : SSet.{u}) :
    {f : T ⟶ E // f ≫ q = SSet.const c} ≃ (T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q c) where
  toFun f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift q c f.val f.property
  invFun f := ⟨f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q c, by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]⟩
  left_inv f := Subtype.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _)
  right_inv f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext q c (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _)

/-- 概要：fiber とパラメータの直積上の図式を定値逆像上の図式へ移す全単射。
方針：定値逆像の同型で前合成する。
規約：全て実際の単体集合の射。
使われ方：関手単体集合のパラメータ付き普遍性との接続。 -/
def constantPullbackHomEquiv {K C : SSet.{u}} (p : K ⟶ C)
    (c : C _⦋0⦌) (T D : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c ⊗ T ⟶ D) ≃ (pullback (SSet.const c : T ⟶ C) p ⟶ D) where
  toFun h := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.constantPullbackIso p c T).hom ≫ h
  invFun h := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.constantPullbackIso p c T).inv ≫ h
  left_inv h := by
    dsimp only
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  right_inv h := by
    dsimp only
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- 概要：fiber ごとの関手の全空間の fiber と、fiber からの関手空間の同じ普遍性。
方針：内部 Hom の随伴、定値逆像の同型、全空間の普遍性、fiber の普遍性を合成する。
規約：任意の単体集合パラメータ T を扱う。
使われ方：fiber の単体集合としての同型の構成。 -/
def fiberwiseHomFiberHomEquiv {K C : SSet.{u}} (p : K ⟶ C)
    (c : C _⦋0⦌) (D T : SSet.{u}) :
    (T ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c)).obj D) ≃
      (T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection p D) c) :=
  ((ihom.adjunction (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c)).homEquiv T D).symm |>.trans
    (constantPullbackHomEquiv p c T D) |>.trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomEquiv p (SSet.const c : T ⟶ C)) |>.trans
    (vertexFiberHomEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection p D) c T)

/-- 概要：fiber の Hom 比較の包含への合成は定値逆像の図式の curry。
方針：比較を定義どおり計算する。
規約：fiber の包含後の厳密な式。
使われ方：パラメータに関する自然性の確認。 -/
lemma fiberwiseHomFiberHomEquiv_apply_ι {K C : SSet.{u}} (p : K ⟶ C)
    (c : C _⦋0⦌) (D T : SSet.{u}) (h : T ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c)).obj D) :
    fiberwiseHomFiberHomEquiv p c D T h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection p D) c =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry p (SSet.const c : T ⟶ C)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.constantPullbackIso p c T).hom ≫ uncurry h) := rfl

/-- 概要：定値逆像上の図式の curry はパラメータの制限と可換。
方針：一般の fiber ごとの族の curry の自然性を使う。
規約：底は同じ頂点 c に固定する。
使われ方：fiber の比較の単体的自然性。 -/
lemma fiberwiseHomCurry_const_precomp {K C T U D : SSet.{u}} (p : K ⟶ C)
    (c : C _⦋0⦌) (i : T ⟶ U) (H : pullback (SSet.const c : U ⟶ C) p ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry p (SSet.const c : T ⟶ C)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map
        (Over.homMk i (by simp only [Over.mk_hom, SSet.comp_const]) :
          Over.mk (SSet.const c : T ⟶ C) ⟶ Over.mk (SSet.const c : U ⟶ C)) ≫ H) =
      i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry p (SSet.const c : U ⟶ C) H :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorCurry_precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p) ⟨SSet.const c, H⟩ i

/-- 概要：fiber の全パラメータ Hom 比較はパラメータの変更に自然。
方針：定値逆像の直積表示の自然性と内部 Hom の随伴の自然性を合わせる。
規約：任意の射 i を扱う。
使われ方：Yoneda により fiber を関手単体集合と厳密に同定する。 -/
lemma fiberwiseHomFiberHomEquiv_naturality {K C T U D : SSet.{u}} (p : K ⟶ C)
    (c : C _⦋0⦌) (i : T ⟶ U) (h : U ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c)).obj D) :
    fiberwiseHomFiberHomEquiv p c D T (i ≫ h) =
      i ≫ fiberwiseHomFiberHomEquiv p c D U h := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection p D) c
  rw [Category.assoc, fiberwiseHomFiberHomEquiv_apply_ι,
    fiberwiseHomFiberHomEquiv_apply_ι, ← fiberwiseHomCurry_const_precomp]
  congr 1
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.constantPullbackIso_naturality, Category.assoc,
    uncurry_natural_left]

/-- 概要：fiber ごとの関手の全空間の c 上の fiber は Fun(K_c,D) に厳密に同型。
方針：全パラメータで自然な Hom の全単射に Yoneda を適用する。
規約：K・C・D の充填性は不要。
使われ方：fiber ごとの普遍余錐を族の制限の fiber の始対象へ移す。 -/
def fiberwiseHomFiberIso {K C : SSet.{u}} (p : K ⟶ C) (c : C _⦋0⦌) (D : SSet.{u}) :
    (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c)).obj D ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection p D) c :=
  Yoneda.ext _ _
    (fun {T} ↦ fiberwiseHomFiberHomEquiv p c D T)
    (fun {T} ↦ (fiberwiseHomFiberHomEquiv p c D T).symm)
    (fun h ↦ (fiberwiseHomFiberHomEquiv p c D _).symm_apply_apply h)
    (fun h ↦ (fiberwiseHomFiberHomEquiv p c D _).apply_symm_apply h)
    (fun i h ↦ fiberwiseHomFiberHomEquiv_naturality p c i h)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
