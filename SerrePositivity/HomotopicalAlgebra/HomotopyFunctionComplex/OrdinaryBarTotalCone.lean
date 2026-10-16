module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarCommaCone
public import SerrePositivity.CategoryTheory.ElementsNaturalPrecomp
public import Mathlib.CategoryTheory.Functor.Currying

/-! # The whole labelled cone with changing row degree

The total element category records the actual comma object, simplicial
degree, and Hom label. Every simplex operator is an actual total element
map, and the cone retains the same degree on its two ends.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra Opposite
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarTotalCone
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (R : RightResolutionMapping.Index C)

abbrev Index := (OrdinaryBarEvaluation.bar R).Elements
abbrev commaFirst : Index R ⥤ OrdinaryBarCenters.Comma R :=
  OrdinaryBarCommaCone.barIndices R ⋙ OrdinaryBarCommaCone.first R
abbrev degrees : Index R ⥤ SimplexCategoryᵒᵖ :=
  Functor.Elements.π (OrdinaryBarEvaluation.bar R)
abbrev firstBase := (commaFirst R).prod' (degrees R)

abbrev values : OrdinaryBarCenters.Comma R × SimplexCategoryᵒᵖ ⥤ Type v :=
  Functor.uncurry.obj (CostructuredArrow.proj OrdinaryResolutionPairs.projection
    ((RightResolutionMapping.projection (C := C)).obj R) ⋙ OrdinaryResolutionPairs.raw)
abbrev Total := (values R).Elements

abbrev firstLabel (s : Index R) : ((firstBase R) ⋙ values R).obj s :=
  (s.val.obj 0).left.val

lemma commaFirst_map_canonical {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m)
    (c : (OrdinaryBarEvaluation.bar R).obj n) :
    ((commaFirst R).map (Functor.Elements.homMk θ rfl :
      (OrdinaryBarEvaluation.bar R).elementsMk n c ⟶
        (OrdinaryBarEvaluation.bar R).elementsMk m
          ((OrdinaryBarEvaluation.bar R).map θ c))).left =
      (c.map (homOfLE (Fin.zero_le (θ.unop.toOrderHom 0)))).left.hom := by
  change (c.map (homOfLE (Fin.zero_le (θ.unop.toOrderHom 0)))).left.hom ≫ 𝟙 _ = _
  exact Category.comp_id _

lemma firstLabel_naturality {s t : Index R} (f : s ⟶ t) :
    ((firstBase R) ⋙ values R).map f (firstLabel R s) = firstLabel R t := by
  rcases s with @⟨n, c⟩
  rcases t with @⟨m, d⟩
  rcases f with ⟨θ, h⟩
  change n ⟶ m at θ
  change (OrdinaryBarEvaluation.bar R).map θ c = d at h
  subst d
  let f : (OrdinaryBarEvaluation.bar R).elementsMk n c ⟶
      (OrdinaryBarEvaluation.bar R).elementsMk m
        ((OrdinaryBarEvaluation.bar R).map θ c) := Functor.Elements.homMk θ rfl
  change ((OrdinaryResolutionPairs.raw (C := C)).obj
      (c.obj (θ.unop.toOrderHom 0)).left.obj).map θ
      (((OrdinaryResolutionPairs.raw (C := C)).map
        ((commaFirst R).map f).left).app n
          (c.obj 0).left.val) = _
  dsimp only [f]
  rw [commaFirst_map_canonical]
  have hl : (((OrdinaryResolutionPairs.raw (C := C)).map
      (c.map (homOfLE (Fin.zero_le (θ.unop.toOrderHom 0)))).left.hom).app n
        (c.obj 0).left.val) = (c.obj (θ.unop.toOrderHom 0)).left.val :=
    (c.map (homOfLE (Fin.zero_le (θ.unop.toOrderHom 0)))).left.map_val
  exact congrArg (fun x => ((OrdinaryResolutionPairs.raw (C := C)).obj
    (c.obj (θ.unop.toOrderHom 0)).left.obj).map θ x) hl

def labels : Index R ⥤ ((firstBase R) ⋙ values R).Elements where
  obj s := ((firstBase R) ⋙ values R).elementsMk s (firstLabel R s)
  map f := Functor.Elements.homMk f (firstLabel_naturality R f)

abbrev first : Index R ⥤ Total R :=
  labels R ⋙ Functor.Elements.precomp (firstBase R) (values R)

variable (a : NerveFirstChoice.System (OrdinaryBarCenters.leftChoices R))
  (b : NerveFirstChoice.System (OrdinaryBarCenters.rightChoices R))

abbrev rowBase :=
  (OrdinaryBarCommaCone.barIndices R ⋙ OrdinaryBarCommaCone.rows R).prod' (degrees R)

abbrev baseCone : firstBase R ⟶ rowBase R :=
  NatTrans.prod' (OrdinaryBarCommaCone.barCone R a b) (𝟙 (degrees R))

abbrev rows : Index R ⥤ Total R :=
  labels R ⋙ (Functor.whiskerRight (baseCone R a b) (values R)).mapElements ⋙
    Functor.Elements.precomp (rowBase R) (values R)

/-- All original labelled simplex comparisons, now one actual natural transformation. -/
abbrev cone : first R ⟶ rows R a b :=
  Functor.whiskerLeft (labels R)
    (ElementsNaturalPrecomp.comparison (values R) (baseCone R a b))

lemma cone_degree (s : Index R) : ((cone R a b).app s).hom.2 = 𝟙 s.obj := rfl

lemma cone_arrow (n : SimplexCategoryᵒᵖ) (c : (OrdinaryBarEvaluation.bar R).obj n) :
    ((cone R a b).app ((OrdinaryBarEvaluation.bar R).elementsMk n c)).hom.1.left =
      OrdinaryBarSimplexCone.arrow R a b n c := rfl

lemma row_label (n : SimplexCategoryᵒᵖ) (c : (OrdinaryBarEvaluation.bar R).obj n) :
    ((rows R a b).obj ((OrdinaryBarEvaluation.bar R).elementsMk n c)).val =
      ((OrdinaryBarEvaluation.evaluation R a b).app n c).down := by
  change ((OrdinaryResolutionPairs.raw (C := C)).obj
    ((OrdinaryResolutionRows.rows R).obj n)).map (𝟙 n)
      (((OrdinaryResolutionPairs.raw (C := C)).map
        (OrdinaryBarSimplexCone.arrow R a b n c)).app n (c.obj 0).left.val) = _
  rw [CategoryTheory.Functor.map_id]
  exact OrdinaryBarSimplexCone.arrow_label R a b n c

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarTotalCone
