module

public import SerrePositivity.KST.Spectra.PointedVerticalChainExtension
public import SerrePositivity.KST.Spectra.KanSequence

/-!
概要：指定した厳密な列への射影を保ち、元の垂直な構造比較の有限鎖から列を厳密化する。
方針：修正鎖を懸垂・標的構造射へ移し、次段を Kan fibration の相対延長で修正する。
規約：全単射 RLP や追加の Ω 条件は不要。使われ方：全パラメータ族の相対厳密化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.KanSequence
variable {X Y Z : KanSequence.{u}} (hX : ∀ n, Mono (X.sigma n).right)
  (q : Hom Y Z) (hq : ∀ n, SSet.modelCategoryQuillen.J.rlp (q.app n).right)
  (b : Hom X Z) (f : ∀ n, (X.level n).space ⟶ (Y.level n).space)
  (hb : ∀ n, f n ≫ q.app n = b.app n)
  (hf : ∀ n, PointedMapping.VerticalChain (q.app (n + 1))
    (X.sigma n ≫ f (n + 1)) (PointedSimplicialSet.circle.{u} ◁ f n ≫ Y.sigma n))

/-- 元の指定した射影と、元の段射からの垂直な修正鎖を保持する帰納状態。 -/
def RelativeRectificationStage (n : ℕ) :=
  { g : (X.level n).space ⟶ (Y.level n).space //
    g ≫ q.app n = b.app n ∧ PointedMapping.VerticalChain (q.app n) (f n) g }

/-- 前段の垂直な修正鎖を境界へ移し、次段の射影を固定して厳密に可換にする。 -/
def relativeRectificationNext (n : ℕ) (s : RelativeRectificationStage q b f n) :
    { t : RelativeRectificationStage q b f (n + 1) //
      X.sigma n ≫ t.val = PointedSimplicialSet.circle.{u} ◁ s.val ≫ Y.sigma n } := by
  let sourceMono : Mono (X.sigma n).right := hX n
  have hs := s.property.2.suspension.post (q.app (n + 1)) (Y.sigma n) (Z.sigma n)
    (q.comm n).symm
  have hc := (hf n).trans hs
  let hex := PointedExtension.exists_adjustment_chain_over
    (q.app (n + 1)) (hq (n + 1)) (X.sigma n) (f (n + 1))
    (PointedSimplicialSet.circle.{u} ◁ s.val ≫ Y.sigma n) (b.app (n + 1)) (hb (n + 1)) hc
  exact ⟨⟨hex.choose, hex.choose_spec.2.1, hex.choose_spec.2.2⟩, hex.choose_spec.1⟩

/-- 零段を保持し、元の射影と垂直な修正鎖を全段に保持する相対帰納構成。 -/
def relativeRectificationStage : (n : ℕ) → RelativeRectificationStage q b f n
  | 0 => ⟨f 0, hb 0, .refl⟩
  | n + 1 => (relativeRectificationNext hX q hq b f hb hf n (relativeRectificationStage n)).val

/-- 元の厳密な列への射影を保つ、垂直なホモトピー可換な段射の厳密化。 -/
def relativeRectify : Hom X Y where
  app n := (relativeRectificationStage hX q hq b f hb hf n).val
  comm n := (relativeRectificationNext hX q hq b f hb hf n
    (relativeRectificationStage hX q hq b f hb hf n)).property.symm

/-- 元の指定した列への射影は、全段で厳密に保持される。 -/
lemma relativeRectify_projection (n : ℕ) :
    (relativeRectify hX q hq b f hb hf).app n ≫ q.app n = b.app n :=
  (relativeRectificationStage hX q hq b f hb hf n).property.1

/-- 元の段射から厳密化した段射への修正は、同じ射影を固定する有限鎖として保持される。 -/
lemma relativeRectify_chain (n : ℕ) : PointedMapping.VerticalChain (q.app n) (f n)
    ((relativeRectify hX q hq b f hb hf).app n) :=
  (relativeRectificationStage hX q hq b f hb hf n).property.2

/-- 相対厳密化後も、元の各段の全パラメータの成分は保持する。 -/
lemma relativeRectify_component (n : ℕ) :
    PointedMapping.componentOf ((relativeRectify hX q hq b f hb hf).app n) =
      PointedMapping.componentOf (f n) :=
  (relativeRectify_chain hX q hq b f hb hf n).component.symm

/-- 零段の元の射は相対厳密化でも厳密に保持する。 -/
lemma relativeRectify_zero : (relativeRectify hX q hq b f hb hf).app 0 = f 0 := rfl

end SerrePositivity.KST.Spectra.KanSequence
