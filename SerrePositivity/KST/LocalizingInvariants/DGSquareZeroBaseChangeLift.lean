module

public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestrictionComposition
public import SerrePositivity.KST.LocalizingInvariants.DGDerivationOfMapOver

/-!
概要：平方零代数への実射を、指定した底の因子分解に沿って厳密に持ち上げる。
方針：元の係数射影の derivation を回収し、制限の合成同型で元の底へ戻す。
規約：底への可換式は実代数射の等式。使われ方：Postnikov 相対経路の共通底。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable {R : Type u} [CommRing R] {A B W : Mon (Complex R)} (q : A ⟶ B)
  (N : Bimod B B)

def baseChangeMap : algebra A (bimoduleRestrict q N) ⟶ algebra B N :=
  mapOver q (bimoduleRestrict q N) N (𝟙 (bimoduleRestrict q N))

lemma baseChangeMap_projection : baseChangeMap q N ≫ projection B N =
    projection A (bimoduleRestrict q N) ≫ q := mapOver_projection _ _ _ _

variable (a : W ⟶ A) (b : W ⟶ algebra B N) (h : b ≫ projection B N = a ≫ q)

def baseChangeLift : W ⟶ algebra A (bimoduleRestrict q N) :=
  (derivationOfMapOver (a ≫ q) N b h).section ≫ mapOver a
    (bimoduleRestrict (a ≫ q) N) (bimoduleRestrict q N) (bimoduleRestrictionCompIso a q N).hom

lemma baseChangeLift_hom : (baseChangeLift q N a b h).hom =
    biprod.lift a.hom (b.hom ≫ (biprod.snd : (algebra B N).X ⟶ N.X)) := by
  change biprod.lift (𝟙 W.X) (b.hom ≫ biprod.snd) ≫
    biprod.map a.hom (𝟙 N.X) = _
  apply biprod.hom_ext <;> simp [Category.assoc]

lemma baseChangeLift_projection : baseChangeLift q N a b h ≫
    projection A (bimoduleRestrict q N) = a := by
  apply Mon.Hom.ext
  change (baseChangeLift q N a b h).hom ≫ biprod.fst = a.hom
  exact (congrArg (fun t => t ≫ (biprod.fst : A.X ⊞ N.X ⟶ A.X))
    (baseChangeLift_hom q N a b h)).trans (biprod.lift_fst _ _)

lemma baseChangeLift_map : baseChangeLift q N a b h ≫ baseChangeMap q N = b := by
  apply Mon.Hom.ext
  change (baseChangeLift q N a b h).hom ≫ biprod.map q.hom (𝟙 N.X) = b.hom
  let c : W.X ⟶ N.X := b.hom ≫ biprod.snd
  have hb : b.hom ≫ (biprod.fst : B.X ⊞ N.X ⟶ B.X) = a.hom ≫ q.hom :=
    congrArg Mon.Hom.hom h
  have he : biprod.lift a.hom c ≫ biprod.map q.hom (𝟙 N.X) =
      (b.hom : W.X ⟶ B.X ⊞ N.X) := by
    apply biprod.hom_ext
    · rw [Category.assoc, biprod.map_fst, ← Category.assoc, biprod.lift_fst]
      exact hb.symm
    · simp only [Category.assoc, biprod.map_snd, Category.comp_id, biprod.lift_snd]
      rfl
  exact (congrArg (fun t => t ≫ biprod.map q.hom (𝟙 N.X))
    (baseChangeLift_hom q N a b h)).trans he

end SerrePositivity.KST.LocalizingInvariants.SquareZero
