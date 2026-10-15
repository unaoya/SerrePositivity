module
public import SerrePositivity.DifferentialGraded.Module.ConeCompositionHomotopy
public import SerrePositivity.DifferentialGraded.Module.DistinguishedTriangles

/-! # 合成cone三角形とそのdistinguished性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
lemma triangle_comp_shift_id_of_eq {C : Type*} [Category* C] [HasShift C ℤ]
    {X Y Z : C} (a : X ⟶ Y⟦(1 : ℤ)⟧) (b : X ⟶ Z) (c : Z ⟶ Y⟦(1 : ℤ)⟧)
    (h : a = b ≫ c) : a ≫ (𝟙 Y)⟦(1 : ℤ)⟧' = b ≫ c := by
  rw [(shiftFunctor C (1 : ℤ)).map_id, Category.comp_id]
  exact h

lemma map_comp_shift_comm {C E : Type*} [Category* C] [Category* E]
    [HasShift C ℤ] [HasShift E ℤ] (F : C ⥤ E) [F.CommShift ℤ]
    {X Y Z : C} (f : X ⟶ Y⟦(1 : ℤ)⟧) (g : Y ⟶ Z) :
    F.map (f ≫ g⟦(1 : ℤ)⟧') ≫ (F.commShiftIso (1 : ℤ)).hom.app Z =
      (F.map f ≫ (F.commShiftIso (1 : ℤ)).hom.app Y) ≫ (F.map g)⟦(1 : ℤ)⟧' := by
  have hn := (F.commShiftIso (1 : ℤ)).hom.naturality g
  change F.map (g⟦(1 : ℤ)⟧') ≫ (F.commShiftIso (1 : ℤ)).hom.app Z =
    (F.commShiftIso (1 : ℤ)).hom.app Y ≫ (F.map g)⟦(1 : ℤ)⟧' at hn
  rw [F.map_comp, Category.assoc, hn, ← Category.assoc]

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleEvaluation_registeredShift (s : ℤ) {M N : ModuleCategory A D}
    (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).map (f⟦s⟧') = ((moduleEvaluation A D x).map f)⟦s⟧' :=
  moduleShiftFunctor_map_eval A D s f x

def moduleConeCompSecondMap {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    moduleCone A D (f ≫ g) ⟶ moduleCone A D g :=
  moduleConeMap A D (f ≫ g) g f (𝟙 P) (by simp)

lemma moduleConeCompSecondMap_eval {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P)
    (x : D) :
    (moduleEvaluation A D x).map (moduleConeCompSecondMap A D f g) =
      CochainComplex.mappingCone.map ((moduleEvaluation A D x).map (f ≫ g))
        ((moduleEvaluation A D x).map g) ((moduleEvaluation A D x).map f)
        (𝟙 ((moduleEvaluation A D x).obj P))
        (by rw [CategoryTheory.Functor.map_comp, Category.comp_id]) := by
  unfold moduleConeCompSecondMap
  simpa only [CategoryTheory.Functor.map_id] using
    moduleConeMap_eval A D (f ≫ g) g f (𝟙 P) (by simp) x

lemma moduleConeComp_inr_inv {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    moduleConeInr A D (moduleConeCompMap A D f g) ≫ moduleConeCompInv A D f g =
      moduleConeCompSecondMap A D f g := by
  apply moduleMorphism_ext
  intro x
  rw [(moduleEvaluation A D x).map_comp, moduleConeInr_eval, moduleConeCompInv_eval]
  exact (complexConeComp_inr_inv ((moduleEvaluation A D x).map f)
    ((moduleEvaluation A D x).map g) ((moduleEvaluation A D x).map (f ≫ g))
    ((moduleEvaluation A D x).map_comp f g)
    ((moduleEvaluation A D x).map (moduleConeCompMap A D f g))
    (moduleConeCompMap_eval A D f g x)).trans (moduleConeCompSecondMap_eval A D f g x).symm

lemma moduleConeComp_hom_connecting {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    moduleConeCompHom A D f g ≫ moduleConeConnecting A D (moduleConeCompMap A D f g) =
      moduleConeConnecting A D g ≫ (moduleConeInr A D f)⟦(1 : ℤ)⟧' := by
  apply moduleMorphism_ext
  intro x
  rw [(moduleEvaluation A D x).map_comp (moduleConeCompHom A D f g)
      (moduleConeConnecting A D (moduleConeCompMap A D f g)),
    moduleConeCompHom_eval, moduleConeConnecting_eval]
  conv_rhs => rw [(moduleEvaluation A D x).map_comp]
  rw [moduleConeConnecting_eval A D g x,
    moduleEvaluation_registeredShift A D 1 (moduleConeInr A D f) x, moduleConeInr_eval A D f x]
  exact complexConeComp_hom_connecting _ _ _ _ _ _

/-- cone(f)→cone(f≫g)→cone(g)→cone(f)[1]。 -/
def moduleConeCompTriangle {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    Triangle (ModuleCategory A D) :=
  Triangle.mk (moduleConeCompMap A D f g) (moduleConeCompSecondMap A D f g)
    (moduleConeConnecting A D g ≫ (moduleConeInr A D f)⟦(1 : ℤ)⟧')

abbrev moduleHomotopyConeCompTriangle {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    Triangle (ModuleHomotopyCategory A D) :=
  (moduleToHomotopy A D).mapTriangle.obj (moduleConeCompTriangle A D f g)

/-- 合成cone三角形の第三射について、商関手のshift比較を含む自然性の等式。 -/
lemma moduleHomotopyConeComp_mor₃ {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    (moduleToHomotopy A D).map (moduleConeConnecting A D g ≫ (moduleConeInr A D f)⟦(1 : ℤ)⟧') ≫
      ((moduleToHomotopy A D).commShiftIso (1 : ℤ)).hom.app (moduleCone A D f) =
        ((moduleToHomotopy A D).map (moduleConeConnecting A D g) ≫
          ((moduleToHomotopy A D).commShiftIso (1 : ℤ)).hom.app N) ≫
          ((moduleToHomotopy A D).map (moduleConeInr A D f))⟦(1 : ℤ)⟧' :=
  map_comp_shift_comm (moduleToHomotopy A D)
    (X := moduleCone A D g) (Y := N) (Z := moduleCone A D f)
    (moduleConeConnecting A D g) (moduleConeInr A D f)

lemma moduleHomotopyConeComp_second_hom {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    (moduleToHomotopy A D).map (moduleConeCompSecondMap A D f g) ≫
      (moduleToHomotopy A D).map (moduleConeCompHom A D f g) =
        (moduleToHomotopy A D).map (moduleConeInr A D (moduleConeCompMap A D f g)) := by
  let Q := moduleToHomotopy A D
  let e := moduleConeCompHomotopyIso A D f g
  have h : Q.map (moduleConeInr A D (moduleConeCompMap A D f g)) ≫ e.inv =
      Q.map (moduleConeCompSecondMap A D f g) := by
    change Q.map (moduleConeInr A D (moduleConeCompMap A D f g)) ≫
      Q.map (moduleConeCompInv A D f g) = Q.map (moduleConeCompSecondMap A D f g)
    rw [← Q.map_comp, moduleConeComp_inr_inv]
  change Q.map (moduleConeCompSecondMap A D f g) ≫ e.hom = _
  rw [← h, Category.assoc, e.inv_hom_id, Category.comp_id]

/-- 合成cone三角形は最初のcone射の標準cone三角形と同型。 -/
def moduleHomotopyConeCompTriangleIso {M N P : ModuleCategory A D} (f : M ⟶ N) (g : N ⟶ P) :
    moduleHomotopyConeCompTriangle A D f g ≅
      moduleHomotopyConeTriangle A D (moduleConeCompMap A D f g) := by
  let Q := moduleToHomotopy A D
  refine Triangle.isoMk _ _ (Iso.refl (Q.obj (moduleCone A D f)))
    (Iso.refl (Q.obj (moduleCone A D (f ≫ g)))) (moduleConeCompHomotopyIso A D f g) ?_ ?_ ?_
  · change Q.map (moduleConeCompMap A D f g) ≫ 𝟙 _ =
      𝟙 _ ≫ Q.map (moduleConeCompMap A D f g)
    rw [Category.comp_id, Category.id_comp]
  · change Q.map (moduleConeCompSecondMap A D f g) ≫ Q.map (moduleConeCompHom A D f g) =
      𝟙 _ ≫ Q.map (moduleConeInr A D (moduleConeCompMap A D f g))
    rw [Category.id_comp]
    exact moduleHomotopyConeComp_second_hom A D f g
  · change (Q.map (moduleConeConnecting A D g ≫ (moduleConeInr A D f)⟦(1 : ℤ)⟧') ≫
      (Q.commShiftIso (1 : ℤ)).hom.app (moduleCone A D f)) ≫
        (𝟙 (Q.obj (moduleCone A D f)))⟦(1 : ℤ)⟧' =
      Q.map (moduleConeCompHom A D f g) ≫
        (Q.map (moduleConeConnecting A D (moduleConeCompMap A D f g)) ≫
          (Q.commShiftIso (1 : ℤ)).hom.app (moduleCone A D f))
    have h := (Q.map_comp (moduleConeCompHom A D f g)
      (moduleConeConnecting A D (moduleConeCompMap A D f g))).symm.trans
        (congrArg (fun a => Q.map a) (moduleConeComp_hom_connecting A D f g))
    apply triangle_comp_shift_id_of_eq
    exact (congrArg (fun a => a ≫ (Q.commShiftIso (1 : ℤ)).hom.app (moduleCone A D f))
      h.symm).trans (Category.assoc _ _ _)

lemma moduleHomotopyConeCompTriangle_distinguished {M N P : ModuleCategory A D}
    (f : M ⟶ N) (g : N ⟶ P) :
    moduleHomotopyConeCompTriangle A D f g ∈ moduleDistinguishedTriangles A D :=
  ⟨moduleCone A D f, moduleCone A D (f ≫ g), moduleConeCompMap A D f g,
    ⟨moduleHomotopyConeCompTriangleIso A D f g⟩⟩

end SerrePositivity.DifferentialGraded
