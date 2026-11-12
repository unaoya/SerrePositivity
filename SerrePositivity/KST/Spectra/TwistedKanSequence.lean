module

public import SerrePositivity.KST.Spectra.KanSequence
public import SerrePositivity.KST.Spectra.PostMappingIsomorphism

/-!
概要：厳密な自己射により Kan 列の構造射を変える構成。
方針：構造射の後で自己射を施し、各段の反復回数を一つずつ増やして比較射を作る。
規約：自己射が全基点の π_* 同型なら Ω 条件も保存する。
使われ方：BF 1978 §2、HTT A.3.3、HA §1.4.2。loop 模型の符号の比較。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra.KanSequence

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：Kan 列の厳密な自己射の反復。
方針：恒等射から始めて段ごとの合成を繰り返す。
規約：列の構造射との厳密な可換性を保持する。
使われ方：BF 1978 §2。段ごとの反復回数を変える比較射。 -/
def iterateHom {X : KanSequence.{u}} (r : Hom X X) : ℕ → Hom X X
  | 0 => { app := fun _ => 𝟙 _, comm := by intro n; simp }
  | m + 1 => (iterateHom r m).comp r

/-- 概要：自己射の反復は各段で全基点の π_* 同型性を保つ。
方針：恒等射と合成の保存を帰納的に使う。
規約：全自然数次数と全ての基点。
使われ方：Goerss–Jardine I §7、BF 1978 §2。構造射を変えた列への比較。 -/
theorem iterateHom_piIsomorphism {X : KanSequence.{u}} (r : Hom X X)
    (hr : ∀ k, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (r.app k).right) (m k : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((iterateHom r m).app k).right := by
  induction m with
  | zero => exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.id _
  | succ m ih =>
    change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (((iterateHom r m).app k).right ≫ (r.app k).right)
    exact ih.comp (hr k)

/-- 概要：厳密な自己射の後合成で構造射を変えた Kan 列。
方針：各段は保ち、σ の後で次段の自己射を施す。
規約：この段階では構造射の単射性を要求しない。
使われ方：BF 1978 §2、HA §1.4.2。符号を変えた loop 模型の構造。 -/
def twist {X : KanSequence.{u}} (r : Hom X X) : KanSequence.{u} where
  level := X.level
  sigma n := X.sigma n ≫ r.app (n + 1)

/-- 概要：元の列から構造射を変えた列への実際の厳密な比較射。
方針：n 段では自己射を n 回施し、可換性で反復回数を一つ増やす。
規約：対合性の厳密な等式は不要。
使われ方：BF 1978 §2、HA §1.4.2。符号変更を実際の射で比較する。 -/
def twistMap {X : KanSequence.{u}} (r : Hom X X) : Hom X (twist r) where
  app n := (iterateHom r n).app n
  comm n := by
    change PointedSimplicialSet.circle.{u} ◁ (iterateHom r n).app n ≫
      (X.sigma n ≫ r.app (n + 1)) = X.sigma n ≫ (iterateHom r (n + 1)).app (n + 1)
    rw [← Category.assoc, (iterateHom r n).comm n, Category.assoc]
    rfl

/-- 概要：構造射を変える比較射は各段で全基点の π_* 同型。
方針：各段の反復の同型性を使う。
規約：全基点の条件を持つ自己射を仮定する。
使われ方：BF 1978 §2。符号変更による同値の各段での検査。 -/
theorem twistMap_piIsomorphism {X : KanSequence.{u}} (r : Hom X X)
    (hr : ∀ k, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (r.app k).right) (k : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((twistMap r).app k).right := iterateHom_piIsomorphism r hr k k

/-- 概要：構造射の後で全基点の π_* 同型を施しても Ω 条件は保たれる。
方針：随伴射を内部 Hom の後合成へ分解し、Kan 値の写像空間での同型保存を使う。
規約：元の列は Ω 条件を満たす。
使われ方：BF 1978 §2、HTT A.3.3、HA §1.4.2。符号を変えた列の fibrant 条件。 -/
theorem twist_omegaCondition {X : KanSequence.{u}} (r : Hom X X)
    (hX : X.OmegaCondition) (hr : ∀ k, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (r.app k).right) :
    (twist r).OmegaCondition := by
  intro n
  have he : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (X.level n).space (X.level (n + 1)).space
      ((twist r).sigma n) =
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (X.level n).space (X.level (n + 1)).space (X.sigma n) ≫
      PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (r.app (n + 1)) :=
    MonoidalClosed.curry_natural_right _ _
  have hpost := PointedMapping.post_piIsomorphism PointedSimplicialSet.circle.{u}
    (r.app (n + 1)) (hr (n + 1))
  change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (X.level n).space
    (X.level (n + 1)).space ((twist r).sigma n)).right
  rw [he]
  exact (hX n).comp hpost

end

end SerrePositivity.KST.Spectra.KanSequence
