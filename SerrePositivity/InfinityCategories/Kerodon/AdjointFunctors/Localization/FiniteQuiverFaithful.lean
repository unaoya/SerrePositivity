module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver
public import Mathlib.Combinatorics.Quiver.Covering

/-!
# 元の有限頂点自由圏の射影の忠実性

概要：有限頂点部分型の包含は元の生成辺と全射列を区別する。
方針：元の出る辺の星の単射性を Mathlib の射列の星の単射性へ移す。
規約：全域の被覆性や有限集合外への辺の持ち上げは要求しない。
使われ方：有限支持へ持ち上げた行の圏の法則を検査する。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (S : Finset Q)

lemma inclusion_star_injective : letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    ∀ x : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S, Function.Injective ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.inclusion S).star x) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  intro x
  rintro ⟨y, f⟩ ⟨z, g⟩ h
  change (⟨y.val, f⟩ : Quiver.Star x.val) = ⟨z.val, g⟩ at h
  obtain ⟨hv, hf⟩ := Sigma.mk.inj_iff.mp h
  have he : y = z := Subtype.ext hv
  subst z
  have he : f = g := eq_of_heq hf
  subst g
  rfl

lemma inclusion_pathStar_injective : letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    ∀ x : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S, Function.Injective ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.inclusion S).pathStar x) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  intro x
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.inclusion S).pathStar_injective (inclusion_star_injective S) x

lemma pathInclusion_faithful : letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S; (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.pathInclusion S).Faithful := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  constructor
  intro x y p q h
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S at x y
  change @Quiver.Path (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S) x y at p q
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.inclusion S).pathStar x ⟨y, p⟩ = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.inclusion S).pathStar x ⟨y, q⟩ := by
    change (⟨y.val, (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.inclusion S).mapPath p⟩ : Quiver.PathStar x.val) =
      ⟨y.val, (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.inclusion S).mapPath q⟩
    exact congrArg (fun r => (⟨y.val, r⟩ : Quiver.PathStar x.val)) h
  have he := inclusion_pathStar_injective S x he
  exact eq_of_heq (Sigma.mk.inj_iff.mp he).2

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
