module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinPrismShuffle
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCylinderNaturality

/-!
概要：prism の最後の最大単体より前の部分から境界 relative join への因子化。
方針：境界の prism、終端、最後より前の最大単体の三種類の生成部分で像を計算する。
規約：ここでは因子化だけを証明し、部分複体の包含の anodyne 性は別に扱う。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、Z(0) と Z(m) の比較の可換な立方体。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：境界の prism と終端を合わせた部分複体 Z(0)。
方針：二つの標準包含の像の和を取る。
規約：係数の標準単体の次元は m。
使われ方：Kerodon Lemma 3.1.2.12（Tag 00TH）、Proposition 5.2.4.5（Tag 024R） の prism の帰納の始点。 -/
noncomputable def relativeJoinPrismInitial (m : ℕ) :
    ((Δ[1] : SSet.{u}) ⊗ Δ[m]).Subcomplex :=
  Subcomplex.range ((Δ[1] : SSet.{u}) ◁ (boundary m).ι) ⊔
    Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[m] : SSet.{u}))

/-- 概要：最後の最大単体を除く prism の生成部分 Z(m)。
方針：Z(0) に切替位置が最後より前の最大単体を全て加える。
規約：m=0 では追加する最大単体はない。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、境界 relative join に写る prism の部分。 -/
noncomputable def relativeJoinPrismPenultimate (m : ℕ) :
    ((Δ[1] : SSet.{u}) ⊗ Δ[m]).Subcomplex :=
  relativeJoinPrismInitial m ⊔
    ⨆ k : {k : Fin (m + 1) // k < Fin.last m},
      Subcomplex.ofSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle m k.val)

/-- 概要：prism の生成部分 Z(m) は初期部分 Z(0) を含む。
方針：部分複体の和の左の包含を使う。
規約：まだ包含の同値性を主張しない。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、prism の分解の最初の射。 -/
lemma relativeJoinPrismInitial_le_penultimate (m : ℕ) :
    relativeJoinPrismInitial.{u} m ≤ relativeJoinPrismPenultimate m := le_sup_left

/-- 概要：Z(m) の比較像は境界の relative join の像に含まれる。
方針：境界 prism と終端では自然性、残る生成単体では切替位置の計算を使う。
規約：構造射 f の終域は任意。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、Z(m) から境界側への射の構成。 -/
lemma relativeJoinPrismPenultimate_le_boundary_preimage {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) :
    relativeJoinPrismPenultimate m ≤
      (Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinLeftMap (𝟙 Y) (f := (boundary m).ι ≫ f) (f' := f)
        (boundary m).ι rfl)).preimage (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism f) := by
  let u : Over.mk ((boundary m).ι ≫ f) ⟶ Over.mk f := Over.homMk (boundary m).ι rfl
  apply sup_le
  · apply sup_le
    · intro n z hz
      obtain ⟨v, rfl⟩ := hz
      refine ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism ((boundary m).ι ≫ f)).app n v, ?_⟩
      exact (congrArg (fun k : (Δ[1] : SSet.{u}) ⊗ (boundary m : SSet.{u}) ⟶
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin f (𝟙 Y) ↦ k.app n v) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism_naturality u))
    · intro n z hz
      obtain ⟨a, rfl⟩ := hz
      refine ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr ((boundary m).ι ≫ f) (𝟙 Y)).app n (f.app n a), ?_⟩
      have hr := congrArg (fun k : Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin f (𝟙 Y) ↦ k.app n (f.app n a))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr_leftMap u)
      have he := congrArg (fun k : (Δ[m] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin f (𝟙 Y) ↦ k.app n a)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism_one f)
      exact hr.trans he.symm
  · apply iSup_le
    intro k
    apply (Subcomplex.ofSimplex_le_iff _ _).mpr
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrismShuffle_mem_boundary f k.val k.property

/-- 概要：Z(m) 上の比較射の像は境界 relative join の像に含まれる。
方針：逆像への包含を制限した射の像の包含へ書き換える。
規約：制限する射は Z(m) の包含と prism 比較の合成。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、境界への因子化の普遍性への入力。 -/
lemma relativeJoinPrismPenultimate_range_le {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) :
    Subcomplex.range ((relativeJoinPrismPenultimate m).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism f) ≤
      Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinLeftMap (𝟙 Y) (f := (boundary m).ι ≫ f) (f' := f)
        (boundary m).ι rfl) := by
  intro n z hz
  obtain ⟨a, rfl⟩ := hz
  exact relativeJoinPrismPenultimate_le_boundary_preimage f n a.property

/-- 概要：Z(m) の比較を境界 relative join へ因子化する射。
方針：像への射を作り、境界の包含が単射であることから像の同型を逆に使う。
規約：構造射 f の終域に quasicategory 性は要求しない。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、prism の分解の立方体の上側の射。 -/
noncomputable def relativeJoinPrismPenultimateBoundaryLift {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) :
    (relativeJoinPrismPenultimate m : SSet.{u}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin ((boundary m).ι ≫ f) (𝟙 Y) :=
  Subcomplex.lift ((relativeJoinPrismPenultimate m).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism f)
    (relativeJoinPrismPenultimate_range_le f) ≫
      inv (Subfunctor.toRange (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinLeftMap (𝟙 Y)
        (f := (boundary m).ι ≫ f) (f' := f) (boundary m).ι rfl))

/-- 概要：Z(m) の境界への因子化は全体への包含後に元の比較に一致する。
方針：像への同型の逆射と包含の合成を計算する。
規約：厳密な射の等式として可換性を得る。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、prism の分解の立方体の可換性。 -/
lemma relativeJoinPrismPenultimateBoundaryLift_comp {Y : SSet.{u}} {m : ℕ}
    (f : (Δ[m] : SSet.{u}) ⟶ Y) :
    relativeJoinPrismPenultimateBoundaryLift f ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinLeftMap (𝟙 Y) (f := (boundary m).ι ≫ f) (f' := f) (boundary m).ι rfl =
      (relativeJoinPrismPenultimate m).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism f := by
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinLeftMap (𝟙 Y) (f := (boundary m).ι ≫ f) (f' := f)
    (boundary m).ι rfl
  have hq : inv (Subfunctor.toRange q) ≫ q = (Subcomplex.range q).ι := by
    calc
      _ = inv (Subfunctor.toRange q) ≫ (Subfunctor.toRange q ≫ (Subcomplex.range q).ι) :=
        congrArg (fun k ↦ inv (Subfunctor.toRange q) ≫ k) (Subfunctor.toRange_ι q).symm
      _ = _ := IsIso.inv_hom_id_assoc _ _
  rw [relativeJoinPrismPenultimateBoundaryLift, Category.assoc, hq]
  exact Subcomplex.lift_ι _ _

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
