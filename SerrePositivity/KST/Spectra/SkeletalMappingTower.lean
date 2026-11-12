module

public import SerrePositivity.KST.Spectra.SkeletalWeightColimit
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

/-!
概要：有限骨格からの写像空間の Kan fibration の塔と全体の写像空間の復元。
方針：骨格の単射の指数版 pushout-product と、反変内部 Hom の極限保存を使う。
規約：係数の Kan 性だけを要求する。ホモトピー群と塔の極限の交換は別工程。
使われ方：Goerss–Jardine VIII §§1–2、Kerodon §3.1.3（Tag 00TJ）。自明作用の hG の塔。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalClosed SSet Opposite
open SSet.modelCategoryQuillen
open HomotopicalAlgebra

namespace SerrePositivity.KST.Spectra.SkeletalMapping

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：有限骨格の増加列を単体集合の図式とする。
方針：部分複体の順序関手から包含を取る。
規約：段 n は通常の n 骨格。
使われ方：Goerss–Jardine VIII §1。写像空間の塔の源。 -/
def source (X : SSet.{u}) : ℕ ⥤ SSet.{u} :=
  (SkeletalWeightedEnd.skeletonOrder X).monotone.functor ⋙ Subcomplex.toSSetFunctor

/-- 概要：有限骨格から係数への写像空間の塔。
方針：骨格の増加列を反変な内部 Hom へ送る。
規約：この定義には係数の Kan 性を要求しない。
使われ方：Goerss–Jardine VIII §§1–2。nerve からの写像空間の段階的な解析。 -/
def tower (X Y : SSet.{u}) : ℕᵒᵖ ⥤ SSet.{u} :=
  (source X).op ⋙ internalHom.flip.obj Y

instance level_kanComplex (X Y : SSet.{u}) [KanComplex Y] (n : ℕᵒᵖ) :
    KanComplex ((tower X Y).obj n) := by
  change KanComplex ((ihom ((X.skeleton (n.unop + 1) : SSet.{u}))).obj Y)
  infer_instance

/-- 概要：有限骨格の写像空間の塔の遷移は Kan fibration。
方針：骨格の包含の単射性を指数版 pushout-product の充填に渡す。
規約：源の単体集合 X の Kan 性は不要。
使われ方：Goerss–Jardine VIII §1、Kerodon §3.1.3（Tag 00TJ）。塔の fiber の長完全列の準備。 -/
theorem map_fibration (X Y : SSet.{u}) [KanComplex Y] {n m : ℕᵒᵖ} (f : n ⟶ m) :
    Fibration ((tower X Y).map f) := by
  change Fibration ((pre (Subcomplex.homOfLE
    (X.skeleton.monotone (Nat.add_le_add_right (leOfHom f.unop) 1)))).app Y)
  infer_instance

/-- 概要：全体の写像空間から骨格の写像空間の塔への錐。
方針：骨格の余錐を反対圏に移して内部 Hom で写す。
規約：頂点は実際の内部 Hom。
使われ方：Goerss–Jardine VIII §1。制限族の整合性。 -/
def cone (X Y : SSet.{u}) : Cone (tower X Y) :=
  (internalHom.flip.obj Y).mapCone (SkeletalWeightedEnd.skeletonCocone X).op

/-- 概要：全体の写像空間は有限骨格の写像空間の塔の厳密な極限。
方針：骨格の余極限と反変内部 Hom の極限保存を合成する。
規約：Kan 条件なしで成立する通常の極限の主張。
使われ方：Goerss–Jardine VIII §1。塔からの写像空間の復元。 -/
def coneIsLimit (X Y : SSet.{u}) : IsLimit (cone X Y) :=
  isLimitOfPreserves (internalHom.flip.obj Y)
    (SkeletalWeightedEnd.skeletonCoconeIsColimit X).op

/-- 概要：全体から各骨格への制限も Kan fibration。
方針：骨格から全体への包含の単射性を指数版の充填に使う。
規約：係数 Y の Kan 性のみを要求する。
使われ方：Goerss–Jardine VIII §1、Kerodon §3.1.3（Tag 00TJ）。全体の制限の fiber。 -/
theorem projection_fibration (X Y : SSet.{u}) [KanComplex Y] (n : ℕᵒᵖ) :
    Fibration ((cone X Y).π.app n) := by
  change Fibration ((pre (X.skeleton (n.unop + 1)).ι).app Y)
  infer_instance

end

end SerrePositivity.KST.Spectra.SkeletalMapping
