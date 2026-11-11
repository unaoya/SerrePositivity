module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinTensor
public import Mathlib.CategoryTheory.Adhesive.Basic
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
概要：部分パラメータの join と左因子全体を貼り合わせた相対的な境界。
方針：左端の逆像を次数ごとに計算し、adhesive な pushout の単射判定を使う。
規約：右因子 K は任意、パラメータの射 i に単射性を課す。
使われ方：Kerodon §4.6.6（Tag 04HY）、写像空間の比較の逆を部分族に関して固定する貼り合わせ。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：join の切断が全頂点数である単体は左包含の像。
方針：依存和の切断を固定し、空の右区間の単体の一意性を使う。
規約：右因子 K の非空性は不要。
使われ方：Kerodon §4.6.6（Tag 04HY）、左端の逆像の計算。 -/
lemma joinSimplex_exists_inl_of_cut {A K : SSet.{u}} {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A K) _⦋n⦌) (h : s.1.val = n + 1) :
    ∃ a : A _⦋n⦌, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A K).app (Opposite.op ⦋n⦌) a = s := by
  rcases s with ⟨⟨c, hc⟩, a, k⟩
  change c = n + 1 at h
  subst c
  refine ⟨a, ?_⟩
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.inl a : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex A K n) = ⟨⟨n + 1, hc⟩, a, k⟩
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.inl a) ⟨⟨n + 1, hc⟩, a, k⟩ rfl rfl ?_
  exact @Subsingleton.elim (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K (n + 1 - (n + 1)))
    (by simp only [Nat.sub_self, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj]; infer_instance) _ _

/-- 概要：部分パラメータの join に左因子全体を貼り合わせた対象。
方針：左端 A を共通部分として A⋆K と B の pushout を取る。
規約：i の単射性を課さず対象を定義する。
使われ方：Kerodon §4.6.6（Tag 04HY）、部分族と固定始点を同時に指定する境界。 -/
noncomputable def joinLeftBoundaryObject {A B : SSet.{u}} (i : A ⟶ B) (K : SSet.{u}) :
    SSet.{u} := pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A K) i

/-- 概要：部分パラメータと左端を貼った対象を全体の join に含める射。
方針：joinMap と左包含を、左端での可換性に沿って貼る。
規約：右因子は恒等で保つ。
使われ方：Kerodon §4.6.6（Tag 04HY）、相対的な逆の選択で固定する図式の包含。 -/
noncomputable def joinLeftBoundaryMap {A B : SSet.{u}} (i : A ⟶ B) (K : SSet.{u}) :
    joinLeftBoundaryObject i K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join B K :=
  pushout.desc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 K)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl B K) (by
    simpa only [Category.id_comp] using _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap i (𝟙 K))

/-- 概要：相対境界の包含は部分パラメータの join 上で joinMap と一致する。
方針：pushout の左包含で貼り合わせを計算する。
規約：i と K は任意。
使われ方：Kerodon §4.6.6（Tag 04HY）、指定された部分族の保持。 -/
lemma joinLeftBoundaryMap_join {A B : SSet.{u}} (i : A ⟶ B) (K : SSet.{u}) :
    pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A K) i ≫ joinLeftBoundaryMap i K = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 K) :=
  pushout.inl_desc _ _ _

/-- 概要：相対境界の包含は左因子全体で左包含と一致する。
方針：pushout の右包含で貼り合わせを計算する。
規約：始点の図式は B 全体で指定できる。
使われ方：Kerodon §4.6.6（Tag 04HY）、全パラメータでの始点の固定。 -/
lemma joinLeftBoundaryMap_left {A B : SSet.{u}} (i : A ⟶ B) (K : SSet.{u}) :
    pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A K) i ≫ joinLeftBoundaryMap i K = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl B K :=
  pushout.inr_desc _ _ _

/-- 概要：部分族と左端を貼った join の相対境界の包含は単射。
方針：各次数で左端の引き戻しを計算し、pushout からの比較の単射判定を使う。
規約：i は単射、右因子 K は任意。
使われ方：Kerodon §4.6.6（Tag 04HY）、固定条件を保つ相対的な延長に必要な包含。 -/
instance joinLeftBoundaryMap_mono {A B : SSet.{u}} (i : A ⟶ B) [Mono i] (K : SSet.{u}) :
    Mono (joinLeftBoundaryMap i K) := by
  have : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 K)) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_mono i (𝟙 K)
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨n⟩⟩
  let d := Opposite.op ⦋n⦌
  let ev := (evaluation SimplexCategoryᵒᵖ (Type u)).obj d
  have hw : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 K) = i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl B K := by
    simpa only [Category.id_comp] using _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap i (𝟙 K)
  have hp : IsPullback ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A K).app d) (i.app d)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 K)).app d) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl B K).app d) := by
    apply (Types.isPullback_iff _ _ _ _).2
    refine ⟨NatTrans.congr_app hw d, ?_, ?_⟩
    · intro a a' h
      exact congrArg Prod.fst (eq_of_heq (Sigma.mk.inj h.1).2)
    · intro s b h
      have hc := congrArg (fun z ↦ z.1.val) h
      change s.1.val = n + 1 at hc
      obtain ⟨a, ha⟩ := joinSimplex_exists_inl_of_cut s hc
      refine ⟨a, ha, ?_⟩
      apply (mono_iff_injective ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl B K).app d)).mp inferInstance
      have hh := ConcreteCategory.congr_hom (C := Type u) (NatTrans.congr_app hw d) a
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 K)).app d ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A K).app d a) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl B K).app d (i.app d a) at hh
      rw [ha] at hh
      exact hh.symm.trans h
  let hs := (IsPushout.of_hasPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A K) i).map ev
  have : Mono (hs.desc ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 K)).app d) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl B K).app d) hp.w) :=
    hs.desc_mono_of_isPullback hp
  have he : hs.desc ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 K)).app d) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl B K).app d) hp.w =
      (joinLeftBoundaryMap i K).app d := by
    apply hs.hom_ext
    · rw [hs.inl_desc]
      exact (NatTrans.congr_app (joinLeftBoundaryMap_join i K) d).symm
    · rw [hs.inr_desc]
      exact (NatTrans.congr_app (joinLeftBoundaryMap_left i K) d).symm
  rw [← he]
  infer_instance

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
