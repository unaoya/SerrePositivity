module

public import Mathlib.CategoryTheory.Triangulated.TStructure.TExact
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT

/-!
# t 完全な関手と切り詰めた射の可逆性

t 完全な三角関手がある射を可逆にするならば、その射の非正切り詰めも可逆にする。
切り詰め三角形の同型の存在と、中央成分による三角形の射の一意性を用いる。
これは局所化に t 構造が降下するための分母条件の必要性を与える。
-/

@[expose] public section

universe v u v' u'

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (t : TStructure C) (s : TStructure D) (F : C ⥤ D)
  [F.CommShift ℤ] [F.IsTriangulated] [F.TExact t s]

include s in
set_option backward.defeqAttrib.useBackward true in
/-- t 完全な関手が可逆にする射は、非正切り詰めの後もその関手で可逆になる。 -/
lemma tExact_isIso_map_truncLE {X Y : C} (f : X ⟶ Y) [IsIso (F.map f)] (n : ℤ) :
    IsIso (F.map ((t.truncLE n).map f)) := by
  let G := t.triangleLEGE n (n + 1) rfl ⋙ F.mapTriangle
  have hX : G.obj X ∈ distTriang D :=
    F.map_distinguished _ (t.triangleLEGE_distinguished n (n + 1) rfl X)
  have hY : G.obj Y ∈ distTriang D :=
    F.map_distinguished _ (t.triangleLEGE_distinguished n (n + 1) rfl Y)
  have hXle : s.IsLE (G.obj X).obj₁ n :=
    Functor.isLE_obj F t s ((t.truncLE n).obj X) n
  have hYle : s.IsLE (G.obj Y).obj₁ n :=
    Functor.isLE_obj F t s ((t.truncLE n).obj Y) n
  have hXge : s.IsGE (G.obj X).obj₃ (n + 1) :=
    Functor.isGE_obj F t s ((t.truncGE (n + 1)).obj X) (n + 1)
  have hYge : s.IsGE (G.obj Y).obj₃ (n + 1) :=
    Functor.isGE_obj F t s ((t.truncGE (n + 1)).obj Y) (n + 1)
  let e₂ : F.obj X ≅ F.obj Y := asIso (F.map f)
  obtain ⟨e, he⟩ := s.triangle_iso_exists hX hY e₂ n (n + 1)
    hXle hXge hYle hYge
  have heq : G.map f = e.hom := s.triangle_map_ext hX hY n (n + 1) hXle hYge
    (by simpa [G, e₂] using he.symm)
  change IsIso (G.map f).hom₁
  rw [heq]
  infer_instance

end SerrePositivity
