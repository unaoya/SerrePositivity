module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FiniteQuiver
public import Mathlib.Combinatorics.Quiver.Covering

/-!
# 元の有限頂点自由圏の射影の忠実性

概要：有限頂点部分型の包含は元の生成辺と全射列を区別する。
方針：元の出る辺の星の単射性を Mathlib の射列の星の単射性へ移す。
規約：全域の被覆性や有限集合外への辺の持ち上げは要求しない。
使われ方：有限支持へ持ち上げた行の圏の法則を検査する。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FiniteQuiver
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (S : Finset Q)

lemma inclusion_star_injective : letI := quiver S
    ∀ x : Vertex S, Function.Injective ((inclusion S).star x) := by
  let := quiver S
  intro x
  rintro ⟨y, f⟩ ⟨z, g⟩ h
  change (⟨y.val, f⟩ : Quiver.Star x.val) = ⟨z.val, g⟩ at h
  obtain ⟨hv, hf⟩ := Sigma.mk.inj_iff.mp h
  have he : y = z := Subtype.ext hv
  subst z
  have he : f = g := eq_of_heq hf
  subst g
  rfl

lemma inclusion_pathStar_injective : letI := quiver S
    ∀ x : Vertex S, Function.Injective ((inclusion S).pathStar x) := by
  let := quiver S
  intro x
  exact (inclusion S).pathStar_injective (inclusion_star_injective S) x

lemma pathInclusion_faithful : letI := quiver S; (pathInclusion S).Faithful := by
  let := quiver S
  constructor
  intro x y p q h
  change Vertex S at x y
  change @Quiver.Path (Vertex S) (quiver S) x y at p q
  have he : (inclusion S).pathStar x ⟨y, p⟩ = (inclusion S).pathStar x ⟨y, q⟩ := by
    change (⟨y.val, (inclusion S).mapPath p⟩ : Quiver.PathStar x.val) =
      ⟨y.val, (inclusion S).mapPath q⟩
    exact congrArg (fun r => (⟨y.val, r⟩ : Quiver.PathStar x.val)) h
  have he := inclusion_pathStar_injective S x he
  exact eq_of_heq (Sigma.mk.inj_iff.mp he).2

end SerrePositivity.EInfinity.Hammock.FiniteQuiver
