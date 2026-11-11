module

public import Mathlib.AlgebraicTopology.SimplicialNerve
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn

/-!
# Coherent nerve のホーンからの対象と Hom の回収

概要：二次元以上のホーンから共通の対象族と整合する面上の Hom 写像を回収する。
方針：頂点で対象を定め、単体的自然性で全ての面と対象を同定する。
規約：Mathlib の `SimplicialNerve` とその ULift を直接使う。局所 Kan 性はまだ不要。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.10（Tag 00LT） の空洞部分への貼合せの準備。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section

universe w v u

open CategoryTheory
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]
variable {n : ℕ} {i : Fin (n + 3)}
/-- 概要：二次元以上のホーンの任意の頂点を零単体として取る。
方針：ホーンが全零単体を含むことを使う。
規約：対象型と Hom の宇宙を区別し、Mathlib の ULift を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.10（Tag 00LT） のホーンの Hom データの貼合せ。 -/
def hornVertex (i : Fin (n + 3)) (a : Fin (n + 3)) :
    (Λ[n + 2, i] : SSet.{w}) _⦋0⦌ :=
  ⟨SSet.stdSimplex.obj₀Equiv.symm a, by rw [SSet.horn_obj_eq_univ i 0 (by omega)]; trivial⟩
/-- 概要：ホーンから coherent nerve の対象族を回収する。
方針：各零単体の像で唯一の対象を評価する。
規約：対象型と Hom の宇宙を区別し、Mathlib の ULift を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.10（Tag 00LT） のホーンの Hom データの貼合せ。 -/
def hornObj (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (a : Fin (n + 3)) : C :=
  (σ.app _ (hornVertex.{max u v} i a)).obj ⟨⟨0⟩⟩
/-- 概要：ホーンの単体の一頂点への制限はその頂点の零単体である。
方針：定値写像による反変作用を計算する。
規約：対象型と Hom の宇宙を区別し、Mathlib の ULift を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.10（Tag 00LT） のホーンの Hom データの貼合せ。 -/
lemma horn_map_const {m : ℕ} (x : (Λ[n + 2, i] : SSet.{w}) _⦋m⦌)
    (a : Fin (m + 1)) :
    (Λ[n + 2, i] : SSet.{w}).map (SimplexCategory.const ⦋0⦌ ⦋m⦌ a).op x =
      hornVertex i (x.1.down.toOrderHom a) := by
  apply Subtype.ext
  rfl
/-- 概要：coherent nerve の単体的作用は対象上で添字の前合成になる。
方針：Mathlib の豊穣関手の合成の定義を展開する。
規約：対象型と Hom の宇宙を区別し、Mathlib の ULift を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.10（Tag 00LT） のホーンの Hom データの貼合せ。 -/
lemma simplex_map_obj {m r : ℕ} (F : (SimplicialNerve C) _⦋r⦌)
    (α : ⦋m⦌ ⟶ ⦋r⦌) (a : Fin (m + 1)) :
    ((SimplicialNerve C).map α.op F).obj ⟨⟨a⟩⟩ = F.obj ⟨⟨α.toOrderHom a⟩⟩ := rfl
/-- 概要：ホーンの各単体の対象は回収した共通の頂点対象に一致する。
方針：ホーンからの写像の自然性を頂点で評価する。
規約：対象型と Hom の宇宙を区別し、Mathlib の ULift を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.10（Tag 00LT） のホーンの Hom データの貼合せ。 -/
lemma horn_simplex_obj (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    {m : ℕ} (x : (Λ[n + 2, i] : SSet.{max u v}) _⦋m⦌) (a : Fin (m + 1)) :
    (σ.app _ x).obj ⟨⟨a⟩⟩ = hornObj σ (x.1.down.toOrderHom a) := by
  have h := NatTrans.naturality_apply σ (SimplexCategory.const ⦋0⦌ ⦋m⦌ a).op x
  have h' := congrArg (fun z ↦ z.obj ⟨⟨0⟩⟩) h
  rw [simplex_map_obj, horn_map_const] at h'
  exact h'.symm
/-- 概要：ホーンの各既知面の対象を共通の頂点対象と同定する。
方針：単体の対象比較を面に適用する。
規約：対象型と Hom の宇宙を区別し、Mathlib の ULift を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.10（Tag 00LT） のホーンの Hom データの貼合せ。 -/
lemma horn_face_obj (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (j : Fin (n + 3)) (hj : j ≠ i) (a : Fin (n + 2)) :
    (σ.app _ (SSet.horn.face i j hj)).obj ⟨⟨a⟩⟩ = hornObj σ (j.succAbove a) :=
  horn_simplex_obj σ (SSet.horn.face i j hj) a
/-- 概要：coherent nerve の単体的作用の Hom 写像を計算する。
方針：Path の再添字関手と元の豊穣関手の合成を展開する。
規約：対象型と Hom の宇宙を区別し、Mathlib の ULift を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.10（Tag 00LT） のホーンの Hom データの貼合せ。 -/
lemma simplex_map_hom {m r : ℕ} (F : (SimplicialNerve C) _⦋r⦌)
    (α : ⦋m⦌ ⟶ ⦋r⦌) (x y : SimplicialThickening (ULift.{v} (Fin (m + 1)))) :
    ((SimplicialNerve C).map α.op F).map x y =
      (SimplicialThickening.functor α.toOrderHom.uliftMap).map x y ≫
        F.map ((SimplicialThickening.functor α.toOrderHom.uliftMap).obj x)
          ((SimplicialThickening.functor α.toOrderHom.uliftMap).obj y) := rfl

/-- 概要：ホーンの単体の Hom 写像を共通の対象族の間で読む。
方針：両端の対象比較を使って Hom 単体集合の型を移送する。
規約：対象型と Hom の宇宙を区別し、Mathlib の ULift を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.10（Tag 00LT） のホーンの Hom データの貼合せ。 -/
def hornHomOnCell (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    {m : ℕ} (x : (Λ[n + 2, i] : SSet.{max u v}) _⦋m⦌) (a b : Fin (m + 1)) :
    nerve (SimplicialThickening.Path (ULift.up.{v} a) (ULift.up.{v} b)) ⟶
      SimplicialCategory.sHom (hornObj σ (x.1.down.toOrderHom a))
        (hornObj σ (x.1.down.toOrderHom b)) :=
  (σ.app _ x).map ⟨⟨a⟩⟩ ⟨⟨b⟩⟩ ≫ eqToHom (by
    rw [horn_simplex_obj σ x a, horn_simplex_obj σ x b])

/-- 概要：共通対象へ移送した Hom 写像を元の型へ戻すと元の写像になる。
方針：互いに逆の等式移送を消去する。
規約：対象型と Hom の宇宙を区別し、Mathlib の ULift を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.10（Tag 00LT） のホーンの Hom データの貼合せ。 -/
lemma hornHomOnCell_transport_back
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    {m : ℕ} (x : (Λ[n + 2, i] : SSet.{max u v}) _⦋m⦌) (a b : Fin (m + 1)) :
    hornHomOnCell σ x a b ≫ eqToHom (by
      rw [horn_simplex_obj σ x a, horn_simplex_obj σ x b]) =
        (σ.app _ x).map ⟨⟨a⟩⟩ ⟨⟨b⟩⟩ := by
  simp [hornHomOnCell]
/-- 概要：移送した Hom 写像は元の Hom 写像と異種等号で一致する。
方針：等式による合成移送の一般補題を使う。
規約：対象型と Hom の宇宙を区別し、Mathlib の ULift を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.10（Tag 00LT） のホーンの Hom データの貼合せ。 -/
lemma hornHomOnCell_heq
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    {m : ℕ} (x : (Λ[n + 2, i] : SSet.{max u v}) _⦋m⦌) (a b : Fin (m + 1)) :
    HEq (hornHomOnCell σ x a b) ((σ.app _ x).map ⟨⟨a⟩⟩ ⟨⟨b⟩⟩) :=
  comp_eqToHom_heq _ _

set_option backward.isDefEq.respectTransparency false in
/-- 概要：回収した Hom 写像はホーン内の単体の全ての制限と整合する。
方針：ホーンからの写像の自然性を豊穣関手の Hom で評価し、両端の移送を消去する。
規約：対象型と Hom の宇宙を区別し、Mathlib の ULift を保持する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR）–2.4.5.10（Tag 00LT） のホーンの Hom データの貼合せ。 -/
lemma hornHomOnCell_naturality
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    {m r : ℕ} (x : (Λ[n + 2, i] : SSet.{max u v}) _⦋r⦌)
    (α : ⦋m⦌ ⟶ ⦋r⦌) (a b : Fin (m + 1)) :
    hornHomOnCell σ ((Λ[n + 2, i] : SSet).map α.op x) a b =
      (SimplicialThickening.functor α.toOrderHom.uliftMap).map ⟨⟨a⟩⟩ ⟨⟨b⟩⟩ ≫
        hornHomOnCell σ x (α.toOrderHom a) (α.toOrderHom b) := by
  have hF := NatTrans.naturality_apply σ α.op x
  have h : HEq
      ((σ.app _ ((Λ[n + 2, i] : SSet).map α.op x)).map ⟨⟨a⟩⟩ ⟨⟨b⟩⟩)
      (((SimplicialNerve C).map α.op (σ.app _ x)).map ⟨⟨a⟩⟩ ⟨⟨b⟩⟩) := by
    have hm (F G : EnrichedFunctor SSet
        (SimplicialThickening (ULift.{v} (Fin (m + 1)))) C) (he : F = G) :
        HEq (F.map ⟨⟨a⟩⟩ ⟨⟨b⟩⟩) (G.map ⟨⟨a⟩⟩ ⟨⟨b⟩⟩) := by
      subst G
      rfl
    exact hm _ _ hF
  rw [simplex_map_hom] at h
  apply eq_of_heq
  refine (hornHomOnCell_heq σ _ a b).trans (h.trans ?_)
  symm
  dsimp only [hornHomOnCell]
  rw [← Category.assoc]
  exact comp_eqToHom_heq _ _

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
