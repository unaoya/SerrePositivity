module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.Columns

/-!
概要：strict 図式の一次元 prefix 成分は元の閉零射である。
方針：通常の nerve 包含の零次数成分を取り出す。
規約：元の始点・終点と閉零加群射を保つ。
使われ方：strict augmentation の一次元係数の相殺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [Category J] (F : J ⥤ ModuleCategory R D)

lemma dgCoherentBarStrictTopRaw_edge (s : (nerve J) _⦋1⦌) :
    coherentDiagramTopRaw (dgCoherentBarStrictDiagram R D F) s =
      (closedHomEquiv R (RightModule R D) (F.obj (s.obj 0)) (F.obj (s.obj 1))
        (F.map (s.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))))).val := by
  exact closedNerveHom_zero _

lemma dgCoherentBarStrictTop_edge (s : (nerve J) _⦋1⦌) :
    coherentDiagramTop (dgCoherentBarStrictDiagram R D F) s =
      (closedHomEquiv R (RightModule R D) (F.obj (s.obj 0)) (F.obj (s.obj 1))
        (F.map (s.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))))).val := by
  rw [coherentDiagramTop, dgCoherentBarStrictTopRaw_edge R D F]
  rfl

lemma dgCoherentBarStrictPrefixHom_edge (s : (nerve J) _⦋1⦌) :
    dgCoherentBarPrefixHom R D (dgCoherentBarStrictDiagram R D F) s 0 (by decide) =
      (closedHomEquiv R (RightModule R D) (F.obj (s.obj 0)) (F.obj (s.obj 1))
        (F.map (s.map (homOfLE (by decide : (0 : Fin 2) ≤ 1))))).val := by
  unfold dgCoherentBarPrefixHom
  rw [dgCoherentBarStrictTop_edge R D F]
  rfl

end SerrePositivity.InfinityCategories
