module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.AllFactorizationSmallFamilies
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.ResolutionArrowActionFunctors

/-!
# 中断した任意モデル源への一般化：AllFactorizationSmallAction

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The old whole factorization square acts on small Hom spaces throughout external contexts。

## 方針（定義・証明）
整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0057][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0057
[plan]: ../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The old whole factorization square acts on small Hom spaces throughout external contexts
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.HomotopyFunctionComplex
open AllFactorizationCoherentSquare

namespace SerrePositivity.HomotopyFunctionComplex.AllFactorizationSmallAction
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (X : FramedResolution C) (Y V : ResolutionObject C) (f : X.inner.base ⟶ Y.base) (g : Y ⟶ V)

abbrev centers := contexts X Y V g ⋙ ResolutionArrowDiagram.fromContext C X Y f
abbrev fiberValues := contexts X Y V g ⋙ MixedChoiceFunctor.fibers X Y f
abbrev fiberIso : centers X Y V f g ⋙ ResolutionArrowDiagram.fibers C ≅
    fiberValues X Y V f g :=
  Functor.isoWhiskerLeft (contexts X Y V g) (ResolutionArrowDiagram.fromContextIso C X Y f)
abbrev tupleParameter := CoherentLiftTuples.obj X.inner Y f
abbrev parameter (m n : ℕ) := tupleParameter X Y f ⊗
  (AllFactorizationSmallFamilies.smallParameter.{v} m 2 ⊗
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk n))
abbrev faceParameter (m n : ℕ) := tupleParameter X Y f ⊗
  (AllFactorizationSmallFamilies.smallParameter.{v} m 1 ⊗
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk n))

abbrev rawFamily (side : Bool) {m n : ℕ} (d : AnchoredChain g m)
    (c : ComposableArrows (Context X V) n) :=
  RelativeChoiceSpace.family (CoherentLiftRelative.vertexInclusion X.inner Y f)
    ((MixedChoiceFunctor.boundary X Y f hcof).app ((contexts X Y V g).obj (c.obj (Fin.last n))))
    (AllFactorizationSmallFamilies.family hcof hfib X Y V f g side d c)

/-- Evaluate the old small choice values in the actual universal lift fibers. -/
def liftFamily (side : Bool) {m n : ℕ} (d : AnchoredChain g m)
    (c : ComposableArrows (Context X V) n) : parameter X Y f m n ⟶
    (ResolutionArrowDiagram.fibers C).obj ((centers X Y V f g).obj (c.obj (Fin.last n))) :=
  rawFamily hcof hfib X Y V f g side d c ≫ (fiberIso X Y V f g).inv.app (c.obj (Fin.last n))

abbrev rawFace (side : Bool) (k : Fin 3) {m n : ℕ} (d : AnchoredChain g m)
    (c : ComposableArrows (Context X V) n) :=
  RelativeChoiceSpace.family (CoherentLiftRelative.vertexInclusion X.inner Y f)
    ((MixedChoiceFunctor.boundary X Y f hcof).app ((contexts X Y V g).obj (c.obj (Fin.last n))))
    (AllFactorizationSmallFamilies.faceFamily hcof hfib X Y V f g side k d c)
abbrev liftFace (side : Bool) (k : Fin 3) {m n : ℕ} (d : AnchoredChain g m)
    (c : ComposableArrows (Context X V) n) := rawFace hcof hfib X Y V f g side k d c ≫
      (fiberIso X Y V f g).inv.app (c.obj (Fin.last n))

lemma raw_external (side : Bool) {m n l : ℕ} (d : AnchoredChain g m)
    (c : ComposableArrows (Context X V) n) (θ : SimplexCategory.mk l ⟶ SimplexCategory.mk n) :
    tupleParameter X Y f ◁ (AllFactorizationSmallFamilies.smallParameter.{v} m 2 ◁
      SSet.stdSimplex.map θ) ≫ rawFamily hcof hfib X Y V f g side d c =
    rawFamily hcof hfib X Y V f g side d ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) ≫
      (fiberValues X Y V f g).map
        (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last l))))) := by
  apply (RelativeChoiceSpace.family_naturality _ _ _ _).symm.trans
  apply (congrArg (RelativeChoiceSpace.family _ _)
    (AllFactorizationSmallFamilies.external_naturality hcof hfib X Y V f g side d c θ)).trans
  exact RelativeChoiceSpace.family_postMap _ _ _ _
    (RelativeChoiceFunctor.boundary_naturality (MixedChoiceFunctor.fibers X Y f)
      (MixedChoiceFunctor.boundary X Y f hcof) ((contexts X Y V g).map
        (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last l))))))) _

lemma lift_external (side : Bool) {m n l : ℕ} (d : AnchoredChain g m)
    (c : ComposableArrows (Context X V) n) (θ : SimplexCategory.mk l ⟶ SimplexCategory.mk n) :
    tupleParameter X Y f ◁ (AllFactorizationSmallFamilies.smallParameter.{v} m 2 ◁
      SSet.stdSimplex.map θ) ≫ liftFamily hcof hfib X Y V f g side d c =
    liftFamily hcof hfib X Y V f g side d ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) ≫
      (ResolutionArrowDiagram.fibers C).map ((centers X Y V f g).map
        (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last l)))))) := by
  change _ ≫ (_ ≫ _) = (_ ≫ _) ≫ _
  rw [← Category.assoc, raw_external, Category.assoc, (fiberIso X Y V f g).inv.naturality]
  rfl

lemma lift_face (side : Bool) (k : Fin 3) {m n : ℕ} (d : AnchoredChain g m)
    (c : ComposableArrows (Context X V) n) :
    tupleParameter X Y f ◁ ((SSet.stdSimplex.obj (SimplexCategory.mk m) ◁ SSet.stdSimplex.δ k) ▷
      SSet.stdSimplex.obj (SimplexCategory.mk n)) ≫ liftFamily hcof hfib X Y V f g side d c =
    liftFace hcof hfib X Y V f g side k d c := by
  change _ ≫ (_ ≫ _) = _ ≫ _
  rw [← Category.assoc]
  apply congrArg (fun z => z ≫ (fiberIso X Y V f g).inv.app (c.obj (Fin.last n)))
  apply (RelativeChoiceSpace.family_naturality _ _ _ _).symm.trans
  exact congrArg (RelativeChoiceSpace.family _ _)
    (AllFactorizationSmallFamilies.family_face hcof hfib X Y V f g side k d c)

abbrev input {n : ℕ} (c : ComposableArrows (Context X V) n) (Z : C) :=
  (ResolutionArrowActionFunctors.input C Z).obj
    (Opposite.op ((centers X Y V f g).obj (c.obj (Fin.last n))))

abbrev output {n : ℕ} (c : ComposableArrows (Context X V) n) (Z : C) : SSet.{v} :=
  (ResolutionArrowActionFunctors.output C hcof hfib Z).obj
    ((centers X Y V f g).obj (c.obj (Fin.last n)))

lemma output_kanComplex {n : ℕ} (c : ComposableArrows (Context X V) n) (Z : C) :
    SSet.KanComplex (output hcof hfib X Y V f g c Z) :=
  KanLiftAction.target_kanComplex _ _ _ _

abbrev tailMap {n l : ℕ} (c : ComposableArrows (Context X V) n)
    (θ : SimplexCategory.mk l ⟶ SimplexCategory.mk n) :=
  (centers X Y V f g).map (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last l)))))

abbrev inputMap {n l : ℕ} (c : ComposableArrows (Context X V) n)
    (θ : SimplexCategory.mk l ⟶ SimplexCategory.mk n) (Z : C) :
    input X Y V f g c Z ⟶ input X Y V f g ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) Z :=
  (ResolutionArrowActionFunctors.input C Z).map (tailMap X Y V f g c θ).op

abbrev outputMap {n l : ℕ} (c : ComposableArrows (Context X V) n)
    (θ : SimplexCategory.mk l ⟶ SimplexCategory.mk n) (Z : C) :
    output hcof hfib X Y V f g ((SimplexCategory.toCat.map θ).toFunctor ⋙ c) Z ⟶
      output hcof hfib X Y V f g c Z :=
  (ResolutionArrowActionFunctors.output C hcof hfib Z).map (tailMap X Y V f g c θ)

def action (side : Bool) {m n : ℕ} (d : AnchoredChain g m)
    (c : ComposableArrows (Context X V) n) (Z : C)
    (t : parameter X Y f m n ⟶ input X Y V f g c Z) :
    parameter X Y f m n ⟶ output hcof hfib X Y V f g c Z :=
  ResolutionArrowActionTransport.kan C hcof hfib
    ((centers X Y V f g).obj (c.obj (Fin.last n))) Z
    (liftFamily hcof hfib X Y V f g side d c) t

def faceAction (side : Bool) (k : Fin 3) {m n : ℕ} (d : AnchoredChain g m)
    (c : ComposableArrows (Context X V) n) (Z : C)
    (t : faceParameter X Y f m n ⟶ input X Y V f g c Z) :
    faceParameter X Y f m n ⟶ output hcof hfib X Y V f g c Z :=
  ResolutionArrowActionTransport.kan C hcof hfib
    ((centers X Y V f g).obj (c.obj (Fin.last n))) Z
    (liftFace hcof hfib X Y V f g side k d c) t

lemma action_face (side : Bool) (k : Fin 3) {m n : ℕ} (d : AnchoredChain g m)
    (c : ComposableArrows (Context X V) n) (Z : C)
    (t : parameter X Y f m n ⟶ input X Y V f g c Z) :
    tupleParameter X Y f ◁ ((SSet.stdSimplex.obj (SimplexCategory.mk m) ◁ SSet.stdSimplex.δ k) ▷
      SSet.stdSimplex.obj (SimplexCategory.mk n)) ≫ action hcof hfib X Y V f g side d c Z t =
    faceAction hcof hfib X Y V f g side k d c Z
      ((tupleParameter X Y f ◁ ((SSet.stdSimplex.obj (SimplexCategory.mk m) ◁
        SSet.stdSimplex.δ k) ▷ SSet.stdSimplex.obj (SimplexCategory.mk n))) ≫ t) := by
  change _ ≫ KanLiftAction.parameterized _ _ _ _ _ _ _ _ = _
  rw [KanLiftAction.parameterized_naturality, lift_face]
  rfl

lemma shared_diagonal {m n : ℕ} (d : AnchoredChain g m)
    (c : ComposableArrows (Context X V) n) (Z : C)
    (t : faceParameter X Y f m n ⟶ input X Y V f g c Z) :
    faceAction hcof hfib X Y V f g true 1 d c Z t =
      faceAction hcof hfib X Y V f g false 1 d c Z t := by
  apply congrArg (fun s => ResolutionArrowActionTransport.kan C hcof hfib
    ((centers X Y V f g).obj (c.obj (Fin.last n))) Z s t)
  apply congrArg (fun s => RelativeChoiceSpace.family _ _ s ≫
    (fiberIso X Y V f g).inv.app (c.obj (Fin.last n)))
  exact AllFactorizationSmallFamilies.shared_diagonal hcof hfib X Y V f g d c

lemma raw_vertices (side : Bool) {m n : ℕ} (d : AnchoredChain g m)
    (c : ComposableArrows (Context X V) n) :
    (CoherentLiftRelative.vertexInclusion X.inner Y f ▷
      (AllFactorizationSmallFamilies.smallParameter.{v} m 2 ⊗
        SSet.stdSimplex.obj (SimplexCategory.mk n))) ≫ rawFamily hcof hfib X Y V f g side d c =
    CoherentLiftRelative.vertices X.inner Y f ◁
      (SSet.stdSimplex.isTerminalObj₀.from _ ≫ RelativeChoiceSpace.pointUnitIso.hom) ≫
      (ρ_ _).hom ≫ (MixedChoiceFunctor.boundary X Y f hcof).app
        ((contexts X Y V g).obj (c.obj (Fin.last n))) :=
  RelativeChoiceSpace.family_fixed_boundary _ _ _

lemma action_external (side : Bool) {m n l : ℕ} (d : AnchoredChain g m)
    (c : ComposableArrows (Context X V) n) (θ : SimplexCategory.mk l ⟶ SimplexCategory.mk n)
    (Z : C) (t : parameter X Y f m n ⟶ input X Y V f g c Z) :
    tupleParameter X Y f ◁ (AllFactorizationSmallFamilies.smallParameter.{v} m 2 ◁
      SSet.stdSimplex.map θ) ≫ action hcof hfib X Y V f g side d c Z t =
    ResolutionArrowActionTransport.kan C hcof hfib
      ((centers X Y V f g).obj (c.obj (θ.toOrderHom (Fin.last l)))) Z
      (liftFamily hcof hfib X Y V f g side d ((SimplexCategory.toCat.map θ).toFunctor ⋙ c))
      (((tupleParameter X Y f ◁ (AllFactorizationSmallFamilies.smallParameter.{v} m 2 ◁
        SSet.stdSimplex.map θ)) ≫ t) ≫
        inputMap X Y V f g c θ Z) ≫
      outputMap hcof hfib X Y V f g c θ Z := by
  change _ ≫ KanLiftAction.parameterized _ _ _ _ _ _ _ _ = _
  rw [KanLiftAction.parameterized_naturality, lift_external]
  exact ResolutionArrowActionFunctors.transport C hcof hfib
    ((centers X Y V f g).map (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last l)))))) Z
    (liftFamily hcof hfib X Y V f g side d ((SimplexCategory.toCat.map θ).toFunctor ⋙ c))
    ((tupleParameter X Y f ◁ (AllFactorizationSmallFamilies.smallParameter.{v} m 2 ◁
      SSet.stdSimplex.map θ)) ≫ t)

lemma lift_factor (side : Bool) {m n l : ℕ} (d : AnchoredChain g m)
    (c : ComposableArrows (Context X V) n) (ψ : SimplexCategory.mk l ⟶ SimplexCategory.mk m) :
    tupleParameter X Y f ◁ ((SSet.stdSimplex.map ψ ▷
      SSet.stdSimplex.obj (SimplexCategory.mk 2)) ▷ SSet.stdSimplex.obj (SimplexCategory.mk n)) ≫
      liftFamily hcof hfib X Y V f g side d c =
    liftFamily hcof hfib X Y V f g side (d.reindex ψ.toOrderHom) c := by
  change _ ≫ (_ ≫ _) = _ ≫ _
  rw [← Category.assoc]
  apply congrArg (fun z => z ≫ (fiberIso X Y V f g).inv.app (c.obj (Fin.last n)))
  apply (RelativeChoiceSpace.family_naturality _ _ _ _).symm.trans
  exact congrArg (RelativeChoiceSpace.family _ _)
    (AllFactorizationSmallFamilies.factor_naturality hcof hfib X Y V f g side d c ψ)

lemma action_factor (side : Bool) {m n l : ℕ} (d : AnchoredChain g m)
    (c : ComposableArrows (Context X V) n) (ψ : SimplexCategory.mk l ⟶ SimplexCategory.mk m)
    (Z : C) (t : parameter X Y f m n ⟶ input X Y V f g c Z) :
    tupleParameter X Y f ◁ ((SSet.stdSimplex.map ψ ▷
      SSet.stdSimplex.obj (SimplexCategory.mk 2)) ▷ SSet.stdSimplex.obj (SimplexCategory.mk n)) ≫
      action hcof hfib X Y V f g side d c Z t =
    action hcof hfib X Y V f g side (d.reindex ψ.toOrderHom) c Z
      ((tupleParameter X Y f ◁ ((SSet.stdSimplex.map ψ ▷
        SSet.stdSimplex.obj (SimplexCategory.mk 2)) ▷
          SSet.stdSimplex.obj (SimplexCategory.mk n))) ≫ t) := by
  change _ ≫ KanLiftAction.parameterized _ _ _ _ _ _ _ _ = _
  rw [KanLiftAction.parameterized_naturality, lift_factor]
  rfl

end SerrePositivity.HomotopyFunctionComplex.AllFactorizationSmallAction
