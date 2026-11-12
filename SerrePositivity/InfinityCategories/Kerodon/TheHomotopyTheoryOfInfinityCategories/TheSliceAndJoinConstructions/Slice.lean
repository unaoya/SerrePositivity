module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：join からの射を単体とする slice と coslice。
方針：固定した因子上の制限が p に一致する射の部分型を用いる。
規約：slice は可変因子を左、coslice は右に置く。quasicategory 性は仮定しない。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.5（Tag 017V） の錐と持ち上げ問題。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：図式 p に対する slice を単体集合として構成する。
方針：n 単体を `join Δ[n] K` からの射で K 上 p に一致するものとし、前合成で引き戻す。
規約：任意の単体集合間の射 p を扱う。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.5（Tag 017V） の図式上の錐。 -/
@[kerodon 017W]
def sliceOver {K X : SSet.{u}} (p : K ⟶ X) : SSet.{u} where
  obj n := {σ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (stdSimplex.obj n.unop) K ⟶ X //
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (stdSimplex.obj n.unop) K ≫ σ = p}
  map α := ↾fun σ ↦ ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.map α.unop) (𝟙 K) ≫ σ.val, by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp]
    exact σ.property⟩
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro σ
    apply Subtype.ext
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.map (𝟙 n.unop)) (𝟙 K) ≫ σ.val = σ.val
    rw [CategoryTheory.Functor.map_id, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_id, Category.id_comp]
  map_comp α β := by
    apply ConcreteCategory.hom_ext
    intro σ
    apply Subtype.ext
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.map (β.unop ≫ α.unop)) (𝟙 K) ≫ σ.val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.map β.unop) (𝟙 K) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.map α.unop) (𝟙 K) ≫ σ.val)
    rw [CategoryTheory.Functor.map_comp]
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp (stdSimplex.map β.unop) (stdSimplex.map α.unop) (𝟙 K) (𝟙 K)
    simp only [Category.id_comp] at h
    rw [h, Category.assoc]

/-- 概要：図式 p に対する coslice を単体集合として構成する。
方針：n 単体を `join K Δ[n]` からの射で K 上 p に一致するものとし、前合成で引き戻す。
規約：可変因子は右側。quasicategory 性は不要。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.5（Tag 017V） の双対的な錐。 -/
@[kerodon 017Y, kerodon 020T]
def sliceUnder {K X : SSet.{u}} (p : K ⟶ X) : SSet.{u} where
  obj n := {σ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (stdSimplex.obj n.unop) ⟶ X //
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K (stdSimplex.obj n.unop) ≫ σ = p}
  map α := ↾fun σ ↦ ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (stdSimplex.map α.unop) ≫ σ.val, by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp]
    exact σ.property⟩
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro σ
    apply Subtype.ext
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (stdSimplex.map (𝟙 n.unop)) ≫ σ.val = σ.val
    rw [CategoryTheory.Functor.map_id, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_id, Category.id_comp]
  map_comp α β := by
    apply ConcreteCategory.hom_ext
    intro σ
    apply Subtype.ext
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (stdSimplex.map (β.unop ≫ α.unop)) ≫ σ.val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (stdSimplex.map β.unop) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (stdSimplex.map α.unop) ≫ σ.val)
    rw [CategoryTheory.Functor.map_comp]
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp (𝟙 K) (𝟙 K) (stdSimplex.map β.unop) (stdSimplex.map α.unop)
    simp only [Category.id_comp] at h
    rw [h, Category.assoc]

/-- 概要：slice の錐をその可変因子の単体に制限する射影。
方針：左包含との合成を Yoneda の同値で X の単体に直す。
規約：任意の図式 p に対する単体集合の射。
使われ方：HTT §2.1.2、Kerodon §4.3.5（Tag 017V） の slice の射影。 -/
@[kerodon 017W]
def sliceOverProjection {K X : SSet.{u}} (p : K ⟶ X) : sliceOver p ⟶ X where
  app n := ↾fun σ ↦ SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (stdSimplex.obj n.unop) K ≫ σ.val)
  naturality _ _ α := by
    apply ConcreteCategory.hom_ext
    intro σ
    change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ K ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.map α.unop) (𝟙 K) ≫ σ.val)) =
      X.map α (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ K ≫ σ.val))
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc]
    exact (SSet.yonedaEquiv_naturality α.unop _).symm

/-- 概要：coslice の錐をその可変因子の単体に制限する射影。
方針：右包含との合成を Yoneda の同値で X の単体に直す。
規約：任意の図式 p に対する単体集合の射。
使われ方：HTT §2.1.2、Kerodon §4.3.5（Tag 017V） の双対的な射影。 -/
@[kerodon 017Y]
def sliceUnderProjection {K X : SSet.{u}} (p : K ⟶ X) : sliceUnder p ⟶ X where
  app n := ↾fun σ ↦ SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K (stdSimplex.obj n.unop) ≫ σ.val)
  naturality _ _ α := by
    apply ConcreteCategory.hom_ext
    intro σ
    change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K _ ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (stdSimplex.map α.unop) ≫ σ.val)) =
      X.map α (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K _ ≫ σ.val))
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.assoc]
    exact (SSet.yonedaEquiv_naturality α.unop _).symm

/-- 概要：頂点 x 上の slice。
方針：x に対応する標準零単体からの射に一般の slice を適用する。
規約：固定図式は `Δ[0] ⟶ X`。
使われ方：HTT §1.2.12、Kerodon §4.6.7（Tag 01LA） の終対象。 -/
@[kerodon 0181]
def sliceOverVertex {X : SSet.{u}} (x : X _⦋0⦌) : SSet.{u} :=
  sliceOver (SSet.yonedaEquiv.symm x)

/-- 概要：頂点 x 下の coslice。
方針：x に対応する標準零単体からの射に一般の coslice を適用する。
規約：固定図式は `Δ[0] ⟶ X`。
使われ方：HTT §1.2.12、Kerodon §4.6.7（Tag 01LA） の始対象。 -/
@[kerodon 0181]
def sliceUnderVertex {X : SSet.{u}} (x : X _⦋0⦌) : SSet.{u} :=
  sliceUnder (SSet.yonedaEquiv.symm x)

/-- 概要：K 上 p に一致する join からの射は、A から slice への射を与える。
方針：A の各単体からの Yoneda 射との join に沿って F を制限する。
規約：余極限の一般論を用いない直接構成。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.5（Tag 017V） の slice の普遍性の一方向。 -/
@[kerodon 0189]
def sliceOverCurry {A K X : SSet.{u}} {p : K ⟶ X}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A K ⟶ X) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A K ≫ F = p) : A ⟶ sliceOver p where
  app _ := ↾fun a ↦ ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm a) (𝟙 K) ≫ F, by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp]
    exact hF⟩
  naturality _ _ α := by
    apply ConcreteCategory.hom_ext
    intro a
    apply Subtype.ext
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm (A.map α a)) (𝟙 K) ≫ F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.map α.unop) (𝟙 K) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm a) (𝟙 K) ≫ F)
    have hy := SSet.yonedaEquiv_symm_naturality_left α.unop a
    simp only [Quiver.Hom.op_unop] at hy
    rw [← hy]
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp (stdSimplex.map α.unop) (SSet.yonedaEquiv.symm a) (𝟙 K) (𝟙 K)
    simp only [Category.id_comp] at h
    rw [h, Category.assoc]

/-- 概要：K 上 p に一致する join からの射は、A から coslice への射を与える。
方針：A の各単体からの Yoneda 射を右因子に適用して F を制限する。
規約：余極限の一般論を用いない直接構成。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.5（Tag 017V） の coslice の普遍性の一方向。 -/
def sliceUnderCurry {A K X : SSet.{u}} {p : K ⟶ X}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K A ⟶ X) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K A ≫ F = p) : A ⟶ sliceUnder p where
  app _ := ↾fun a ↦ ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (SSet.yonedaEquiv.symm a) ≫ F, by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp]
    exact hF⟩
  naturality _ _ α := by
    apply ConcreteCategory.hom_ext
    intro a
    apply Subtype.ext
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (SSet.yonedaEquiv.symm (A.map α a)) ≫ F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (stdSimplex.map α.unop) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 K) (SSet.yonedaEquiv.symm a) ≫ F)
    have hy := SSet.yonedaEquiv_symm_naturality_left α.unop a
    simp only [Quiver.Hom.op_unop] at hy
    rw [← hy]
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp (𝟙 K) (𝟙 K) (stdSimplex.map α.unop) (SSet.yonedaEquiv.symm a)
    simp only [Category.id_comp] at h
    rw [h, Category.assoc]

/-- 概要：slice への射に付いた各単体の錐を評価して、join の単体を X に送る。
方針：左区間が非空ならその単体 a の錐を `(ℓ,id,k)` で評価し、空なら p を使う。
規約：これは次数ごとの写像であり、単体作用との可換性は別に示す。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.5（Tag 017V） の普遍性の直接構成。 -/
def sliceOverUncurryApp {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ sliceOver p) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A K) _⦋n⦌ → X _⦋n⦌
  | ⟨⟨0, _⟩, _, k⟩ => p.app _ k
  | ⟨⟨r + 1, hr⟩, a, k⟩ =>
    (f.app _ a).val.app _
      ⟨⟨r + 1, hr⟩, stdSimplex.objEquiv.symm (𝟙 ⦋r⦌), k⟩

/-- 概要：直接評価は固定された右因子上で p に一致する。
方針：切断零の分岐を計算する。
規約：任意の slice への射を扱う。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.5（Tag 017V） の普遍性の固定条件。 -/
lemma sliceOverUncurryApp_inr {A K X : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ sliceOver p) (n : ℕ) (k : K _⦋n⦌) :
    sliceOverUncurryApp f n ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A K).app _ k) = p.app _ k := rfl

/-- 概要：join からの射を各単体に制限してから直接評価すると元の射の成分に戻る。
方針：切断零では固定条件、非空左区間では Yoneda 射の恒等単体での値を使う。
規約：全ての次数と全ての join の単体についての等式。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.5（Tag 017V） の普遍性の逆関係。 -/
lemma sliceOverUncurryApp_curry {A K X : SSet.{u}} {p : K ⟶ X}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A K ⟶ X) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A K ≫ F = p) (n : ℕ) (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A K) _⦋n⦌) :
    sliceOverUncurryApp (sliceOverCurry F hF) n s = F.app _ s := by
  rcases s with ⟨⟨r, hr⟩, a, k⟩
  cases r with
  | zero =>
    exact (ConcreteCategory.congr_hom
      (congrArg (fun g : K ⟶ X ↦ g.app (Opposite.op ⦋n⦌)) hF) k).symm
  | succ r =>
    change F.app _
        ⟨⟨r + 1, hr⟩, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (SSet.yonedaEquiv.symm a) (r + 1)
          (stdSimplex.objEquiv.symm (𝟙 ⦋r⦌)), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (𝟙 K) _ k⟩ =
      F.app _ ⟨⟨r + 1, hr⟩, a, k⟩
    apply congrArg
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ ?_ ?_ ?_
    · rfl
    · exact SSet.yonedaEquiv_symm_app_id a
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom_id K _ k

/-- 概要：左の標準単体の恒等単体と k を組にした join の単体。
方針：切断を r+1 に取り、左因子を標準 r 単体の恒等写像にする。
規約：n は全体の次数、r は左因子の次数。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.5（Tag 017V） の直接評価の生成元。 -/
def sliceOverGenerator (K : SSet.{u}) (n r : ℕ) (hr : r + 1 ≤ n + 1)
    (k : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K (n + 1 - (r + 1))) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[r] : SSet.{u}) K n :=
  ⟨⟨r + 1, by omega⟩, stdSimplex.objEquiv.symm (𝟙 ⦋r⦌), k⟩

/-- 概要：生成元を引き戻し、左区間が空になった場合は右包含だけになる。
方針：切断零での単体作用の式を使う。
規約：切断の等式 hc を明示する。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.5（Tag 017V） の直接評価の自然性の空区間。 -/
lemma sliceOverGenerator_map_zero (K : SSet.{u}) {m n r : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (hr : r + 1 ≤ n + 1)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α (r + 1) = 0) (k : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K (n + 1 - (r + 1))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap Δ[r] K α (sliceOverGenerator K n r hr k) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[r] K).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap K (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMapAt α (r + 1) 0 hc) k) := by
  dsimp only [sliceOverGenerator]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap_eq_at Δ[r] K α _ 0 hc]
  rfl

/-- 概要：生成元を引き戻して左区間が非空なら、制限した標準単体の像になる。
方針：指定した切断での単体作用を計算し、左右の因子を比較する。
規約：新しい左因子の次数は c。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.5（Tag 017V） の直接評価の自然性の非空区間。 -/
lemma sliceOverGenerator_map_succ (K : SSet.{u}) {m n r c : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (hr : r + 1 ≤ n + 1)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α (r + 1) = c + 1) (k : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K (n + 1 - (r + 1))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap Δ[r] K α (sliceOverGenerator K n r hr k) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.leftMapAt α (r + 1) (c + 1) hc)))
        (𝟙 K)).app (Opposite.op ⦋m⦌)
        (sliceOverGenerator K m c (by have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_le α (r + 1); omega)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap K (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMapAt α (r + 1) (c + 1) hc) k)) := by
  dsimp only [sliceOverGenerator]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap_eq_at Δ[r] K α _ (c + 1) hc]
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ ?_ ?_ ?_
  · rfl
  · rfl
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom_id K _ _).symm

/-- 概要：slice への射の直接評価は単体作用と可換。
方針：左区間が空なら p の自然性、非空なら各錐の自然性と f の自然性を使う。
規約：逆像の左区間が空の場合は各錐の固定条件を適用する。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.5（Tag 017V） の普遍性の逆写像。 -/
lemma sliceOverUncurryApp_naturality {A K X : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ sliceOver p) {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A K) _⦋n⦌) :
    sliceOverUncurryApp f m (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap A K α s) =
      X.map (SimplexCategory.mkHom α).op (sliceOverUncurryApp f n s) := by
  rcases s with ⟨⟨r, hr⟩, a, k⟩
  cases r with
  | zero =>
    have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_zero α
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap_eq_at A K α ⟨0, hr⟩ 0 hc]
    have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMapAt α 0 0 hc = α := by
      ext b
      change (α ⟨0 + b.val, _⟩).val - 0 = (α b).val
      simp
    change p.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap K (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMapAt α 0 0 hc) k) =
      X.map (SimplexCategory.mkHom α).op (p.app _ k)
    rw [hb]
    exact ConcreteCategory.congr_hom (p.naturality (SimplexCategory.mkHom α).op) k
  | succ r =>
    let σ := f.app (Opposite.op ⦋r⦌) a
    have hrle : r + 1 ≤ n + 1 := Nat.le_of_lt_succ hr
    have hσ := ConcreteCategory.congr_hom
      (σ.val.naturality (SimplexCategory.mkHom α).op) (sliceOverGenerator K n r hrle k)
    change σ.val.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap Δ[r] K α (sliceOverGenerator K n r hrle k)) =
      X.map (SimplexCategory.mkHom α).op (σ.val.app _ (sliceOverGenerator K n r hrle k)) at hσ
    cases hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α (r + 1) with
    | zero =>
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap_eq_at A K α ⟨r + 1, hr⟩ 0 hc]
      change p.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap K (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMapAt α (r + 1) 0 hc) k) = _
      rw [sliceOverGenerator_map_zero K α hrle hc k] at hσ
      have hp := ConcreteCategory.congr_hom
        (congrArg (fun g : K ⟶ X ↦ g.app (Opposite.op ⦋m⦌)) σ.property)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap K (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMapAt α (r + 1) 0 hc) k)
      exact hp.symm.trans hσ
    | succ c =>
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap_eq_at A K α ⟨r + 1, hr⟩ (c + 1) hc]
      let β := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.leftMapAt α (r + 1) (c + 1) hc
      have hf := congrArg Subtype.val
        (ConcreteCategory.congr_hom (f.naturality (SimplexCategory.mkHom β).op) a)
      change (f.app _ (A.map (SimplexCategory.mkHom β).op a)).val =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.map (SimplexCategory.mkHom β)) (𝟙 K) ≫ σ.val at hf
      change (f.app _ (A.map (SimplexCategory.mkHom β).op a)).val.app (Opposite.op ⦋m⦌)
          (sliceOverGenerator K m c (by have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_le α (r + 1); omega)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap K (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMapAt α (r + 1) (c + 1) hc) k)) = _
      rw [hf]
      rw [sliceOverGenerator_map_succ K α hrle hc k] at hσ
      exact hσ

/-- 概要：slice への射を、K 上 p に一致する join からの射に束ねる。
方針：各次数で `(ℓ,a,k)` を a の錐の `(ℓ,id,k)` での値に送り、自然性補題を使う。
規約：余極限の一般論を使わない直接構成。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.5（Tag 017V） の slice の普遍性。 -/
def sliceOverUncurry {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ sliceOver p) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A K ⟶ X where
  app n := ↾sliceOverUncurryApp f n.unop.len
  naturality _ _ α := ConcreteCategory.hom_ext _ _ (fun s ↦
    sliceOverUncurryApp_naturality f α.unop.toOrderHom s)

/-- 概要：束ねた射は固定された K 上で p に一致する。
方針：右包含上の直接評価の式を各次数で使う。
規約：追加の仮定はない。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.5（Tag 017V） の普遍性の固定条件。 -/
lemma sliceOverUncurry_fixed {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ sliceOver p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A K ≫ sliceOverUncurry f = p := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro k
  rfl

/-- 概要：各単体 a の Yoneda 射に沿って束ねた射を制限すると、a に付いた錐を回収する。
方針：左区間が空なら固定条件、非空なら f の自然性と Yoneda 射の単体作用を使う。
規約：任意の A の単体、任意の次数の join の単体についての等式。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.5（Tag 017V） の普遍性の逆関係。 -/
lemma sliceOverUncurryApp_yoneda {A K X : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ sliceOver p) {n d : ℕ} (a : A _⦋n⦌) (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join Δ[n] K) _⦋d⦌) :
    sliceOverUncurryApp f d ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm a) (𝟙 K)).app _ s) =
      (f.app _ a).val.app _ s := by
  rcases s with ⟨⟨r, hr⟩, x, k⟩
  cases r with
  | zero =>
    have hs : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm a) (𝟙 K)).app (Opposite.op ⦋d⦌)
        (⟨⟨0, hr⟩, x, k⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex Δ[n] K d) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.inr k := by
      refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ ?_ ?_ ?_
      · rfl
      · exact @Subsingleton.elim PUnit inferInstance _ _
      · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom_id K _ k
    rw [hs]
    have hp := ConcreteCategory.congr_hom
      (congrArg (fun g : K ⟶ X ↦ g.app (Opposite.op ⦋d⦌)) (f.app _ a).property) k
    change p.app _ k = _
    have hx : x = PUnit.unit := @Subsingleton.elim PUnit inferInstance _ _
    subst x
    exact hp.symm
  | succ r =>
    let β := stdSimplex.objEquiv x
    have hs : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm a) (𝟙 K)).app (Opposite.op ⦋d⦌)
        (⟨⟨r + 1, hr⟩, x, k⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex Δ[n] K d) =
        ⟨⟨r + 1, hr⟩, A.map β.op a, k⟩ := by
      refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ ?_ ?_ ?_
      · rfl
      · rfl
      · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom_id K _ k
    rw [hs]
    have hf := congrArg Subtype.val (ConcreteCategory.congr_hom (f.naturality β.op) a)
    change (f.app _ (A.map β.op a)).val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.map β) (𝟙 K) ≫ (f.app _ a).val at hf
    change (f.app _ (A.map β.op a)).val.app (Opposite.op ⦋d⦌)
        (sliceOverGenerator K d r (Nat.le_of_lt_succ hr) k) = _
    rw [hf]
    change (f.app _ a).val.app (Opposite.op ⦋d⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.map β) (𝟙 K)).app _
          (sliceOverGenerator K d r (Nat.le_of_lt_succ hr) k)) = _
    apply congrArg
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ ?_ ?_ ?_
    · rfl
    · change stdSimplex.objEquiv.symm ((𝟙 ⦋r⦌) ≫ β) = x
      rw [Category.id_comp]
      exact stdSimplex.objEquiv.symm_apply_apply x
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom_id K _ k

/-- 概要：slice の普遍性。A から slice への射と、K 上 p に一致する join からの射は同値。
方針：各単体の錐を直接評価して束ね、逆は Yoneda 射との join に沿って制限する。
規約：任意の単体集合 A を扱い、余極限の一般論も quasicategory 性も用いない。
使われ方：HTT §1.2.8・2.1.2、Kerodon §4.3.5（Tag 017V） のホーン持ち上げ問題の翻訳。 -/
@[kerodon 0189]
def sliceOverEquiv {A K X : SSet.{u}} (p : K ⟶ X) :
    (A ⟶ sliceOver p) ≃ {F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A K ⟶ X // _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A K ≫ F = p} where
  toFun f := ⟨sliceOverUncurry f, sliceOverUncurry_fixed f⟩
  invFun F := sliceOverCurry F.val F.property
  left_inv f := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    apply Subtype.ext
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro s
    exact sliceOverUncurryApp_yoneda f a s
  right_inv F := by
    apply Subtype.ext
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact sliceOverUncurryApp_curry F.val F.property n.unop.len s

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
