module

public import SerrePositivity.KST.Comparison.IntervalBoundaryFamily
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneIntervalEndpoints
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-!
# anodyne 包含に沿う基底上の相対ホモトピー

概要：anodyne 包含の像を固定し、Kan fibration の基底も固定するホモトピーを作る。
方針：包含と区間境界の pushout-product に horn の右持ち上げ性を適用する。
規約：Segal 1974 Proposition 1.6・Lemma 1.7 の基底付き比較の補助補題。
使われ方：右射の Kan 分解が引き戻しで与える比較の検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
open SerrePositivity.SimplicialModel

/--
概要：点との直積への標準同型は第一射影の切断である。
方針：各単体の第一成分を評価する。
規約：Segal 1974 Lemma 1.7 の区間端点の規約。
使われ方：境界の頂点での計算をホモトピーの端点へ戻す。
-/
theorem pointTensorIso_fst (T : SSet.{u}) :
    (AnodyneHomotopy.pointTensorIso T).hom ≫ fst T (Δ[0] : SSet.{u}) = 𝟙 T := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/--
概要：anodyne 包含上で一致する二つの基底上の射を、包含と基底を固定して結ぶ。
方針：区間境界と包含の pushout-product の anodyne 性から持ち上げる。
規約：Segal 1974 Proposition 1.6・Lemma 1.7。逆元やモデル構造の公理は使わない。
使われ方：Kan 分解のファイバーごとの相対収縮。
-/
theorem anodyne_fiberwise_homotopy {A T E B : SSet.{u}} (i : A ⟶ T)
    (hi : SSet.anodyneExtensions i) (p : E ⟶ B) (hp : SSet.modelCategoryQuillen.J.rlp p)
    (f g : T ⟶ E) (a : A ⟶ E) (hf : i ≫ f = a) (hg : i ≫ g = a)
    (q : T ⟶ B) (hfp : f ≫ p = q) (hgp : g ≫ p = q) :
    ∃ H : SSet.Homotopy f g,
      i ▷ (Δ[1] : SSet.{u}) ≫ H.h = fst A (Δ[1] : SSet.{u}) ≫ a ∧
      H.h ≫ p = fst T (Δ[1] : SSet.{u}) ≫ q := by
  let pp := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i (SSet.boundary.{u} 1).ι
  have hpp : SSet.anodyneExtensions pp.ι := SSet.anodyneExtensions_pushoutObjObjι' pp hi
  have : HasLiftingProperty pp.ι p := hpp _ hp
  let v := fst A (Δ[1] : SSet.{u}) ≫ a
  let base := fst T (Δ[1] : SSet.{u}) ≫ q
  have hc : i ▷ (SSet.boundary.{u} 1) ≫ intervalBoundaryMap f g =
      A ◁ (SSet.boundary.{u} 1).ι ≫ v := by
    rw [intervalBoundaryMap_precomp, hf, hg, intervalBoundaryMap_self]
    rfl
  let u := pp.isPushout.desc (intervalBoundaryMap f g) v hc
  have ha : a ≫ p = i ≫ q := by rw [← hf, Category.assoc, hfp]
  have hbase₀ : intervalBoundaryMap f g ≫ p = T ◁ (SSet.boundary.{u} 1).ι ≫ base := by
    rw [intervalBoundaryMap_postcomp, hfp, hgp, intervalBoundaryMap_self]
    rfl
  have hbase₁ : v ≫ p = i ▷ (Δ[1] : SSet.{u}) ≫ base := by
    dsimp only [v, base]
    rw [Category.assoc, ha]
    exact (whiskerRight_fst_assoc i _ q).symm
  have hu : u ≫ p = pp.ι ≫ base := by
    apply pp.isPushout.hom_ext
    · rw [← Category.assoc, pp.isPushout.inl_desc, ← Category.assoc, pp.inl_ι]
      exact hbase₀
    · rw [← Category.assoc, pp.isPushout.inr_desc, ← Category.assoc, pp.inr_ι]
      exact hbase₁
  let sq : CommSq u pp.ι p base := ⟨hu⟩
  have hb : T ◁ (SSet.boundary.{u} 1).ι ≫ sq.lift = intervalBoundaryMap f g := by
    rw [show T ◁ (SSet.boundary.{u} 1).ι = pp.inl ≫ pp.ι from pp.inl_ι.symm,
      Category.assoc, sq.fac_left]
    exact pp.isPushout.inl_desc _ _ _
  have hr : i ▷ (Δ[1] : SSet.{u}) ≫ sq.lift = v := by
    rw [show i ▷ (Δ[1] : SSet.{u}) = pp.inr ≫ pp.ι from pp.inr_ι.symm,
      Category.assoc, sq.fac_left]
    exact pp.isPushout.inr_desc _ _ _
  have hzero : T ◁ SSet.stdSimplex.δ.{u} (1 : Fin 2) ≫ sq.lift = fst T (Δ[0] : SSet.{u}) ≫ f := by
    have h := congrArg (fun k => T ◁ SSet.boundary.ι.{u} (1 : Fin 2) ≫ k) hb
    rw [← Category.assoc, ← whiskerLeft_comp, SSet.boundary.ι_ι, intervalBoundaryMap_zero] at h
    exact h
  have hone : T ◁ SSet.stdSimplex.δ.{u} (0 : Fin 2) ≫ sq.lift = fst T (Δ[0] : SSet.{u}) ≫ g := by
    have h := congrArg (fun k => T ◁ SSet.boundary.ι.{u} (0 : Fin 2) ≫ k) hb
    rw [← Category.assoc, ← whiskerLeft_comp, SSet.boundary.ι_ι, intervalBoundaryMap_one] at h
    exact h
  refine ⟨{ h := sq.lift, h₀ := ?_, h₁ := ?_, rel := ?_ }, hr, sq.fac_right⟩
  · rw [AnodyneHomotopy.endpoint_zero_factor, Category.assoc, hzero,
      ← Category.assoc, pointTensorIso_fst, Category.id_comp]
    rfl
  · rw [AnodyneHomotopy.endpoint_one_factor, Category.assoc, hone,
      ← Category.assoc, pointTensorIso_fst, Category.id_comp]
    rfl
  · apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property
/--
概要：anodyne な基底上の包含は、元の右射も Kan fibration なら基底上で収縮する。
方針：元の fibration への持ち上げで厳密なレトラクションを作り、相対ホモトピーで収縮する。
規約：Segal 1974 Proposition 1.6・Lemma 1.7 の置換の比較。
使われ方：右射の Kan 分解を引き戻しても局所化同型となること。
-/
theorem anodyne_fibration_retraction {A T B : SSet.{u}} (i : A ⟶ T)
    (hi : SSet.anodyneExtensions i) (g : A ⟶ B) (hg : SSet.modelCategoryQuillen.J.rlp g)
    (p : T ⟶ B) (hp : SSet.modelCategoryQuillen.J.rlp p) (h : i ≫ p = g) :
    ∃ r : T ⟶ A, i ≫ r = 𝟙 A ∧ r ≫ g = p ∧
      ∃ H : SSet.Homotopy (𝟙 T) (r ≫ i),
        i ▷ (Δ[1] : SSet.{u}) ≫ H.h = fst A (Δ[1] : SSet.{u}) ≫ i ∧
        H.h ≫ p = fst T (Δ[1] : SSet.{u}) ≫ p := by
  have : HasLiftingProperty i g := hi _ hg
  let sq : CommSq (𝟙 A) i g p := ⟨by simpa only [Category.id_comp] using h.symm⟩
  have hir : i ≫ sq.lift = 𝟙 A := sq.fac_left
  have hrp : sq.lift ≫ g = p := sq.fac_right
  have hrip : (sq.lift ≫ i) ≫ p = p := by rw [Category.assoc, h, hrp]
  obtain ⟨H, hrel, hbase⟩ := anodyne_fiberwise_homotopy i hi p hp (𝟙 T) (sq.lift ≫ i) i
    (Category.comp_id i) (by rw [← Category.assoc, hir, Category.id_comp]) p
    (Category.id_comp p) hrip
  exact ⟨sq.lift, hir, hrp, H, hrel, hbase⟩


end SerrePositivity.KST.Comparison
