module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceTetrahedronIsoHoms
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceTetrahedronTriangleSquare

/-!
概要：coherent 三単体の四面の指定関手同型の合成則。
方針：指定辺の可換正方形を同型の順方向の射の等式へ移す。
規約：四面は同じ元の三単体から読み、六つの辺の関手を保持する。
使われ方：全錐の比較円柱に沿う二脚の比較の整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：面 013 と前合成した面 123 の合成は、面 023 と後合成した面 012 の合成。
方針：各同型の順方向の射を元の指定辺の類へ戻す。
規約：同型の存在でなく、指定された四面の同型の合成の等式。
使われ方：引き戻し錐の指定可換性を比較ホモトピーに沿って追跡する。 -/
lemma spaceInfinityTetrahedronIso_square (s : SpaceInfinity.{u} _⦋3⦌) :
    spaceInfinityTetrahedronIso013 s ≪≫
        (spaceInfinityTriangleIso (SpaceInfinity.δ 0 s)).precomp
          (show (s.obj ⟨ULift.up 0⟩).obj ⟶ (s.obj ⟨ULift.up 1⟩).obj from
            spaceInfinityTetrahedron01 s) =
      spaceInfinityTetrahedronIso023 s ≪≫
        (spaceInfinityTetrahedronIso012 s).postcomp (spaceInfinityTetrahedron23 s) := by
  apply Iso.ext
  change (spaceInfinityTetrahedronIso013 s).hom ≫ _ =
    (spaceInfinityTetrahedronIso023 s).hom ≫ _
  rw [spaceInfinityTetrahedronPre123_hom, spaceInfinityTetrahedronPost012_hom,
    spaceInfinityTetrahedronIso013_hom, spaceInfinityTetrahedronIso023_hom]
  exact spaceInfinityTetrahedron_triangle_square s

end SerrePositivity.InfinityCategories.F2
