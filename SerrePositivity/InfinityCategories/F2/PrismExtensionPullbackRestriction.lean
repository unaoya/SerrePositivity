module

public import SerrePositivity.InfinityCategories.F2.PrismExtensionEndpointRestriction
public import SerrePositivity.InfinityCategories.F2.RelativeFunctorBaseChangeInverseRestriction
public import SerrePositivity.InfinityCategories.F2.RelativeFunctorRestrictionTransport

/-!
概要：prism の指定終点を引き戻しに表示する操作と始域の制限を交換する。
方針：終点制限・底の表示変更・底変換の逆の三つの自然性を合成する。
規約：元の終点評価と元の底変換を保持。使われ方：指定比較の各 fiber への移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {A C E B K D : SSet.{u}} (p : E ⟶ B)
  (d : ((Δ[1] : SSet.{u}) ⊗ A) ⊗ K ⟶ B) (v : A ⊗ K ⟶ E)
  (hv : v ≫ p = (prismEndpoint 0 A ▷ K) ≫ d) (s : C ⟶ A ⊗ K)
  (q : D ⟶ B) (a : A ⊗ K ⟶ D) (hj : (prismEndpoint 1 A ▷ K) ≫ d = a ≫ q)

include hj in
/-- 同じ終点表示の等式を、区間を保った始域制限に沿って移す。 -/
lemma prismExtensionPullbackRestriction_endpoint :
    prismEndpoint 1 C ≫ prismParameterRestriction s ≫ d = (s ≫ a) ≫ q := by
  change (s ≫ (prismEndpoint 1 A ▷ K)) ≫ d = _
  rw [Category.assoc, hj, Category.assoc]

/-- 引き戻しへ戻した元の終点評価は、始域制限と厳密に可換する。 -/
lemma prismExtensionPullbackEndpoint_restrict :
    relativeFunctorExtensionEndpoint p d (prismEndpoint 0 A ▷ K) v hv
        (prismEndpoint 1 A ▷ K) q a hj ≫
      relativeFunctorOverPre (pullback.snd p q)
        (Over.homMk (U := Over.mk (s ≫ a)) (V := Over.mk a) s rfl) =
    prismExtensionRestriction p d v hv s ≫
      relativeFunctorExtensionEndpoint p (prismParameterRestriction s ≫ d)
        (prismEndpoint 0 C) (s ≫ v) (by rw [Category.assoc, hv]; rfl)
        (prismEndpoint 1 C) q (s ≫ a)
        (prismExtensionPullbackRestriction_endpoint d s q a hj) := by
  let f : Over.mk (s ≫ a) ⟶ Over.mk a := Over.homMk s rfl
  have hi := relativeFunctorBaseChangeInverse_overPre p q f
  change relativeFunctorPre p (a ≫ q) s ≫
      (relativeFunctorBaseChangeIso p q (s ≫ a)).inv =
    (relativeFunctorBaseChangeIso p q a).inv ≫
      relativeFunctorOverPre (pullback.snd p q) f at hi
  have ht := relativeFunctorPre_transport p hj s
  have he := prismExtensionEndpoint_restrict p d v hv s
  change (prismExtensionEndpoint p d v hv ≫
      eqToHom (congrArg (relativeFunctorSpace p) hj) ≫
        (relativeFunctorBaseChangeIso p q a).inv) ≫
      relativeFunctorOverPre (pullback.snd p q) f = _
  simp only [Category.assoc]
  rw [← hi]
  change prismExtensionEndpoint p d v hv ≫
      eqToHom (congrArg (relativeFunctorSpace p) hj) ≫
        relativeFunctorPre p (a ≫ q) s ≫ (relativeFunctorBaseChangeIso p q (s ≫ a)).inv = _
  rw [← Category.assoc (eqToHom _) (relativeFunctorPre p (a ≫ q) s), ht]
  simp only [Category.assoc]
  rw [← Category.assoc (prismExtensionEndpoint p d v hv), he]
  rfl

end SerrePositivity.InfinityCategories.F2
