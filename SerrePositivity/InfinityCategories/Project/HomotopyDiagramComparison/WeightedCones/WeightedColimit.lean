module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.End
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
概要：単体集合の一般の小図式の重み付き余極限を実際の coend として構成する。
方針：反変重みと共変図式の tensor の coend を取り、閉構造で Hom の普遍性を証明する。
規約：重みは Iᵒᵖ、図式は I 上。モデル構造・Kan 性・余極限の普遍性を仮定しない。
使われ方：HTT 4.2.4.1、γ3c の一般の homotopy 余極限の対象と Hom 比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped MonoidalClosed
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {I : Type u} [SmallCategory I]

/-- coend の二変数図式。対角成分の順序は F_i ⊗ W_i。 -/
def weightedColimitDiagram (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) :
    Iᵒᵖ ⥤ I ⥤ SSet.{u} :=
  W ⋙ (curriedTensor SSet.{u}).flip ⋙ (Functor.whiskeringLeft I SSet.{u} SSet.{u}).obj F

/-- 任意の小図式と反変重みの実際の重み付き余極限。 -/
def weightedColimit (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) : SSet.{u} :=
  coend (weightedColimitDiagram W F)

/-- 重み付き余極限の普遍的な重み付き脚。 -/
def weightedColimitι (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) (i : I) :
    F.obj i ⊗ W.obj (Opposite.op i) ⟶ weightedColimit W F :=
  coend.ι (weightedColimitDiagram W F) i

/-- 脚の dinaturality。重みの前合成と図式の後合成を同一視する。 -/
lemma weightedColimit_condition (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u})
    {i j : I} (f : i ⟶ j) :
    F.obj i ◁ W.map f.op ≫ weightedColimitι W F i =
      F.map f ▷ W.obj (Opposite.op j) ≫ weightedColimitι W F j :=
  coend.condition (weightedColimitDiagram W F) f

/-- 重み付き余極限からの射は普遍的な脚との合成で決まる。 -/
lemma weightedColimit_hom_ext {W : Iᵒᵖ ⥤ SSet.{u}} {F : I ⥤ SSet.{u}} {Y : SSet.{u}}
    {f g : weightedColimit W F ⟶ Y}
    (h : ∀ i, weightedColimitι W F i ≫ f = weightedColimitι W F i ≫ g) : f = g :=
  coend.hom_ext h

/-- 反変な Hom 係数図式。写像空間は core を取らない実際の内部 Hom。 -/
abbrev weightedColimitHomDiagram (F : I ⥤ SSet.{u}) (Y : SSet.{u}) : Iᵒᵖ ⥤ SSet.{u} :=
  F.op ⋙ (internalHom (C := SSet.{u})).flip.obj Y

/-- 余極限からの射を各重みから内部 Hom への自然変換へ移す。 -/
def weightedColimitHomTo {W : Iᵒᵖ ⥤ SSet.{u}} {F : I ⥤ SSet.{u}} {Y : SSet.{u}}
    (f : weightedColimit W F ⟶ Y) : W ⟶ weightedColimitHomDiagram F Y where
  app i := curry (weightedColimitι W F i.unop ≫ f)
  naturality i j g := by
    change W.map g ≫ curry (weightedColimitι W F j.unop ≫ f) =
      curry (weightedColimitι W F i.unop ≫ f) ≫ (pre (F.map g.unop)).app Y
    rw [← curry_natural_left, curry_pre_app]
    apply congrArg curry
    simpa only [Category.assoc, Quiver.Hom.op_unop, Opposite.op_unop] using
      congrArg (fun k ↦ k ≫ f) (weightedColimit_condition W F g.unop)

/-- 重みから Hom への自然変換を coend の射へ戻す。 -/
def weightedColimitHomFrom {W : Iᵒᵖ ⥤ SSet.{u}} {F : I ⥤ SSet.{u}} {Y : SSet.{u}}
    (s : W ⟶ weightedColimitHomDiagram F Y) : weightedColimit W F ⟶ Y :=
  coend.desc (fun i ↦ uncurry (s.app (Opposite.op i))) (by
    intro i j f
    change F.obj i ◁ W.map f.op ≫ uncurry (s.app (Opposite.op i)) =
      F.map f ▷ W.obj (Opposite.op j) ≫ uncurry (s.app (Opposite.op j))
    rw [← uncurry_natural_left, ← uncurry_pre_app]
    apply congrArg uncurry
    exact s.naturality f.op)

/-- coend の射を普遍脚で評価すると元の成分の uncurry。 -/
lemma weightedColimitι_homFrom {W : Iᵒᵖ ⥤ SSet.{u}} {F : I ⥤ SSet.{u}} {Y : SSet.{u}}
    (s : W ⟶ weightedColimitHomDiagram F Y) (i : I) :
    weightedColimitι W F i ≫ weightedColimitHomFrom s = uncurry (s.app (Opposite.op i)) :=
  coend.ι_desc _ _ i

/-- coend への降下と Hom への移送は一方の両逆。 -/
lemma weightedColimitHomTo_from {W : Iᵒᵖ ⥤ SSet.{u}} {F : I ⥤ SSet.{u}} {Y : SSet.{u}}
    (s : W ⟶ weightedColimitHomDiagram F Y) :
    weightedColimitHomTo (weightedColimitHomFrom s) = s := by
  apply NatTrans.ext
  funext i
  change curry (weightedColimitι W F i.unop ≫ weightedColimitHomFrom s) = s.app i
  rw [weightedColimitι_homFrom, curry_uncurry]

/-- Hom への移送と coend への降下は他方の両逆。 -/
lemma weightedColimitHomFrom_to {W : Iᵒᵖ ⥤ SSet.{u}} {F : I ⥤ SSet.{u}} {Y : SSet.{u}}
    (f : weightedColimit W F ⟶ Y) :
    weightedColimitHomFrom (weightedColimitHomTo f) = f := by
  apply weightedColimit_hom_ext
  intro i
  rw [weightedColimitι_homFrom]
  exact uncurry_curry _

/-- 実際の重み付き余極限の通常の Hom 普遍性。 -/
def weightedColimitHomEquiv (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) (Y : SSet.{u}) :
    (weightedColimit W F ⟶ Y) ≃ (W ⟶ weightedColimitHomDiagram F Y) where
  toFun := weightedColimitHomTo
  invFun := weightedColimitHomFrom
  left_inv := weightedColimitHomFrom_to
  right_inv := weightedColimitHomTo_from

/-- tensor を各成分へ適用した coend 図式。 -/
def weightedColimitTensorDiagram (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) (A : SSet.{u}) :
    Iᵒᵖ ⥤ I ⥤ SSet.{u} :=
  weightedColimitDiagram W F ⋙ (Functor.whiskeringRight I SSet.{u} SSet.{u}).obj (tensorRight A)

/-- tensor 後の普遍的な cowedge。 -/
def weightedColimitTensorCowedge (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) (A : SSet.{u}) :
    Cowedge (weightedColimitTensorDiagram W F A) :=
  Cowedge.mk (weightedColimit W F ⊗ A) (fun i ↦ weightedColimitι W F i ▷ A) (by
    intro i j f
    change (F.obj i ◁ W.map f.op) ▷ A ≫ weightedColimitι W F i ▷ A =
      (F.map f ▷ W.obj (Opposite.op j)) ▷ A ≫ weightedColimitι W F j ▷ A
    rw [← comp_whiskerRight, ← comp_whiskerRight, weightedColimit_condition])

/-- tensor は coend の普遍性を保つ。完全なモデル構造は不要。 -/
def weightedColimitTensorCowedge_isColimit (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u})
    (A : SSet.{u}) : IsColimit (weightedColimitTensorCowedge W F A) := by
  have h := isColimitOfPreserves (tensorRight A)
    (colimit.isColimit (multispanIndexCoend (weightedColimitDiagram W F)).multispan)
  let e : (multispanIndexCoend (weightedColimitDiagram W F)).multispan ⋙ tensorRight A ≅
      (multispanIndexCoend (weightedColimitTensorDiagram W F A)).multispan :=
    NatIso.ofComponents (fun j ↦ by cases j <;> exact Iso.refl _) (by
      rintro (_ | _) (_ | _) (_ | _ | _) <;> simp [weightedColimitTensorDiagram])
  apply (IsColimit.precomposeHomEquiv e (weightedColimitTensorCowedge W F A)).toFun
  apply IsColimit.ofIsoColimit h
  refine Cocone.ext (Iso.refl _) ?_
  intro j
  cases j <;>
    simp [weightedColimitTensorCowedge, weightedColimitι, coend.ι, e, weightedColimitTensorDiagram]

/-- 図式の自然変換は同じ重みの coend の射を誘導する。 -/
def weightedColimitMap (W : Iᵒᵖ ⥤ SSet.{u}) {F G : I ⥤ SSet.{u}} (η : F ⟶ G) :
    weightedColimit W F ⟶ weightedColimit W G :=
  coend.desc (fun i ↦ η.app i ▷ W.obj (Opposite.op i) ≫ weightedColimitι W G i) (by
    intro i j f
    change F.obj i ◁ W.map f.op ≫ η.app i ▷ W.obj (Opposite.op i) ≫ weightedColimitι W G i =
      F.map f ▷ W.obj (Opposite.op j) ≫ η.app j ▷ W.obj (Opposite.op j) ≫ weightedColimitι W G j
    rw [whisker_exchange_assoc, weightedColimit_condition]
    rw [← comp_whiskerRight_assoc, ← η.naturality f, comp_whiskerRight_assoc])

/-- coend の誘導射は普遍脚で元の自然変換に一致する。 -/
lemma weightedColimitι_map (W : Iᵒᵖ ⥤ SSet.{u}) {F G : I ⥤ SSet.{u}} (η : F ⟶ G) (i : I) :
    weightedColimitι W F i ≫ weightedColimitMap W η =
      η.app i ▷ W.obj (Opposite.op i) ≫ weightedColimitι W G i :=
  coend.ι_desc _ _ i

/-- 重み付き coend は任意の小図式の圏上の関手。 -/
def weightedColimitFunctor (W : Iᵒᵖ ⥤ SSet.{u}) : (I ⥤ SSet.{u}) ⥤ SSet.{u} where
  obj F := weightedColimit W F
  map η := weightedColimitMap W η
  map_id F := by
    apply weightedColimit_hom_ext
    intro i
    rw [weightedColimitι_map]
    simp
  map_comp η θ := by
    apply weightedColimit_hom_ext
    intro i
    rw [weightedColimitι_map, ← Category.assoc, weightedColimitι_map, Category.assoc,
      weightedColimitι_map]
    simp only [NatTrans.comp_app, comp_whiskerRight, Category.assoc]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
