module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderDiagrams

/-!
# 通常の前面と指定した最後の Hom を持つ coherent 錐の全 Hom

概要：元の前面の順序図式に一つの終点を加え、最後への指定 Hom を保持する。
方針：非終点間は元の通常射に定値、終点の自己 Hom は豊穣単位にする。
規約：指定 Hom の合成条件は別に検証し、全 path を保持する。
使われ方：native roof の混合円柱の一つの豊穣図式への組立。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom
open CategoryTheory SimplicialThickening SSet MonoidalCategory CartesianMonoidalCategory
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {n : ℕ}
  (F : Fin (n + 1) ⥤ C) (Y : C)

abbrev vertex (i : Fin (n + 2)) : SimplicialThickening (ULift.{u} (Fin (n + 2))) :=
  ⟨ULift.up i⟩

def obj (i : Fin (n + 2)) : C := Fin.lastCases Y F.obj i

omit [SimplicialCategory C] in
lemma obj_cast (i : Fin (n + 1)) : obj F Y i.castSucc = F.obj i :=
  Fin.lastCases_castSucc i

omit [SimplicialCategory C] in
lemma obj_last : obj F Y (Fin.last (n + 1)) = Y := Fin.lastCases_last

lemma front_le (i j : Fin (n + 1)) (P : vertex.{u} i.castSucc ⟶ vertex j.castSucc) :
    i ≤ j := by
  have h := Path.le P
  change i.castSucc ≤ j.castSucc at h
  exact Fin.castSucc_le_castSucc_iff.mp h

def frontHom (i j : Fin (n + 1)) :
    SimplicialCategory.sHom (vertex.{u} i.castSucc) (vertex j.castSucc) ⟶
      SimplicialCategory.sHom (F.obj i) (F.obj j) where
  app d := ↾fun P => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' _ _
    (F.map (homOfLE (front_le i j (P.obj 0))))) d.unop.len
  naturality {d e} α := by
    apply ConcreteCategory.hom_ext
    intro P
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant_pullback (SimplicialCategory.homEquiv' _ _
      (F.map (homOfLE (front_le i j (P.obj 0))))) α.unop).symm

lemma frontHom_const (i j : Fin (n + 1)) (hij : i ≤ j) :
    frontHom F i j = toUnit _ ≫ eHomEquiv SSet.{u} (F.map (homOfLE hij)) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro P
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' _ _ (F.map (homOfLE hij))) d =
    (eHomEquiv SSet.{u} (F.map (homOfLE hij))).app _ PUnit.unit
  simpa only [SimplicialCategory.homEquiv', Equiv.trans_apply] using
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.unitHom_app_constant (eHomEquiv SSet.{u} (F.map (homOfLE hij))) d).symm

variable (L : ∀ i : Fin (n + 1),
  SimplicialCategory.sHom (vertex.{u} i.castSucc) (vertex (Fin.last (n + 1))) ⟶
    SimplicialCategory.sHom (F.obj i) Y)

def hom (i j : Fin (n + 2)) : SimplicialCategory.sHom (vertex.{u} i) (vertex j) ⟶
    SimplicialCategory.sHom (obj F Y i) (obj F Y j) := by
  induction i using Fin.lastCases <;> induction j using Fin.lastCases
  · simp only [obj, Fin.lastCases_last]
    exact toUnit _ ≫ eId SSet Y
  · rename_i j
    simp only [obj, Fin.lastCases_last, Fin.lastCases_castSucc]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomEmptyMap j _
  · rename_i i
    simp only [obj, Fin.lastCases_last, Fin.lastCases_castSucc]
    exact L i
  · rename_i i j
    simp only [obj, Fin.lastCases_castSucc]
    exact frontHom F i j

lemma hom_last_last : hom F Y L (Fin.last (n + 1)) (Fin.last (n + 1)) ≫
    eqToHom (congrArg₂ SimplicialCategory.sHom (obj_last F Y) (obj_last F Y)) =
      toUnit _ ≫ eId SSet Y := by
  simp -implicitDefEqProofs +instances [hom, obj_last, Category.assoc]

lemma hom_cast_last (i : Fin (n + 1)) : hom F Y L i.castSucc (Fin.last (n + 1)) ≫
    eqToHom (congrArg₂ SimplicialCategory.sHom (obj_cast F Y i) (obj_last F Y)) = L i := by
  simp -implicitDefEqProofs +instances [hom, obj_cast, obj_last, Category.assoc]

lemma hom_cast_cast (i j : Fin (n + 1)) : hom F Y L i.castSucc j.castSucc ≫
    eqToHom (congrArg₂ SimplicialCategory.sHom (obj_cast F Y i) (obj_cast F Y j)) =
      frontHom F i j := by
  simp -implicitDefEqProofs +instances [hom, obj_cast, Category.assoc]

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom
