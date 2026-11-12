module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalAnodyneRecognition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction

/-!
概要：包含を固定する終点への収縮から right anodyne 性を得る。
方針：最後の一次ホーンと包含の pushout-product の矢の retract として表示する。
規約：ホモトピーの向きは恒等から retract の像へ。元の射は単射。
使われ方：Kerodon Proposition 7.2.3.10（Tag 02P6）、終点 fiber による cofinality の生成元の計算。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：最後の一次ホーンとの積は prism の終点だけを通る。
方針：唯一のホーン頂点の値が一であることを全単体で検査する。
規約：A は任意の単体集合。
使われ方：right anodyne な pushout-product の retract の可換性。 -/
lemma cofinalLastHorn_prism_factorization (A : SSet.{u}) :
    ((horn 1 1).ι ▷ A) = snd (horn 1 1 : SSet.{u}) A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, a⟩
  apply Prod.ext
  · apply stdSimplex.ext
    intro k
    obtain ⟨j, hj, hm⟩ := (mem_horn_iff_notMem_range t.val (1 : Fin 2)).1 t.property
    have hj₀ : j = 0 := by
      apply Fin.ext
      change j.val = 0
      have h : j.val ≠ 1 := fun h ↦ hj (Fin.ext h)
      have := j.isLt
      omega
    subst j
    have hk : t.val k ≠ 0 := fun h ↦ hm ⟨k, h⟩
    apply Fin.ext
    have : (t.val k).val ≠ 0 := fun h ↦ hk (Fin.ext h)
    have := (t.val k).isLt
    change (t.val k).val = 1
    omega
  · rfl

/-- 概要：包含を固定する終点への収縮を持つ単射は right anodyne。
方針：最後の一次ホーンとの pushout-product から矢の retract を構成する。
規約：J は区間を第一因子に持ち、時刻零は恒等、時刻一は r≫i。
使われ方：left fibration の終点 fiber の包含と right cofinality。 -/
lemma rightAnodyneExtensions_of_fixed_terminal_homotopy {A B : SSet.{u}}
    (i : A ⟶ B) [Mono i] (r : B ⟶ A) (hir : i ≫ r = 𝟙 A)
    (J : (Δ[1] : SSet.{u}) ⊗ B ⟶ B)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ≫ J = 𝟙 B)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B ≫ J = r ≫ i)
    (hfix : (Δ[1] ◁ i) ≫ J = snd (Δ[1] : SSet.{u}) A ≫ i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions i := by
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) (horn 1 1).ι i
  have hw : ((horn 1 1).ι ▷ A) ≫ snd (Δ[1] : SSet.{u}) A =
      ((horn 1 1 : SSet.{u}) ◁ i) ≫ (snd (horn 1 1 : SSet.{u}) B ≫ r) := by
    rw [whiskerRight_snd, ← Category.assoc, whiskerLeft_snd, Category.assoc, hir,
      Category.comp_id]
  let q := sq.isPushout.desc (snd (Δ[1] : SSet.{u}) A)
    (snd (horn 1 1 : SSet.{u}) B ≫ r) hw
  have hqi : q ≫ i = sq.ι ≫ J := by
    apply sq.hom_ext
    · rw [← Category.assoc, sq.isPushout.inl_desc, ← Category.assoc, sq.inl_ι]
      exact hfix.symm
    · rw [← Category.assoc, sq.isPushout.inr_desc, ← Category.assoc, sq.inr_ι]
      change (snd (horn 1 1 : SSet.{u}) B ≫ r) ≫ i = ((horn 1 1).ι ▷ B) ≫ J
      rw [cofinalLastHorn_prism_factorization]
      simp only [Category.assoc, h₁]
  let t := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ sq.inl
  have ht : t ≫ sq.ι = i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B := by
    rw [Category.assoc, sq.inl_ι]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality 0 i
  have htop : t ≫ q = 𝟙 A := by
    rw [Category.assoc, sq.isPushout.inl_desc]
    rfl
  let re : RetractArrow i sq.ι :=
    { i := Arrow.homMk' t (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B) ht
      r := Arrow.homMk' q J hqi
      retract := by
        apply Arrow.hom_ext
        · exact htop
        · exact h₀ }
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions.of_retract re
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.rightAnodyneExtensions_pushoutObjObj_point i sq)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
