module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FreeQuiverCoverConnected

/-!
# 元の被覆の正向き射列と自由圏の射の回収

概要：元の被覆から自由圏の関手を構成し、元の正向き射列の終点を回収する。
方針：元の生成矢の等式を元の射列の長さで反復する。
規約：元の有向射列・終点・元の groupoid の矢を保持する。
使われ方：元の hammock の全縦射の一意な持ち上げ。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q]

def positiveEvaluation : Paths Q ⥤ Quiver.FreeGroupoid Q := Paths.lift (Quiver.FreeGroupoid.of Q)

lemma positiveEvaluation_cons {X Y Z : Q} (p : Quiver.Path X Y) (f : Y ⟶ Z) :
    positiveEvaluation.map (p.cons f) =
      positiveEvaluation.map p ≫ (Quiver.FreeGroupoid.of Q).map f :=
  Paths.lift_cons _ _ _

variable (A : Q)

def pathProjection : letI := quiver A; Paths (Vertex A) ⥤ Paths Q := by
  letI := quiver A
  exact Cat.freeMap (projection A)

lemma positive_endpoint (x y : Vertex A) :
    letI := quiver A
    ∀ p : Quiver.Path x y,
      x.path ≫ positiveEvaluation.map ((projection A).mapPath p) = y.path := by
  let := quiver A
  intro p
  induction p with
  | nil =>
    exact (congrArg (fun q => x.path ≫ q) (positiveEvaluation.map_id x.base)).trans
      (Category.comp_id x.path)
  | @cons y z p f ih =>
    change x.path ≫ positiveEvaluation.map (((projection A).mapPath p).cons f.val) = z.path
    rw [positiveEvaluation_cons, ← Category.assoc, ih]
    exact f.property

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
