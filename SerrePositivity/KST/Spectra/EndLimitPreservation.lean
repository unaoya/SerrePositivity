module

public import Mathlib.CategoryTheory.Limits.Shapes.End
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
概要：二変数図式の end 関手は通常の極限を保つ。
方針：各成分の極限への持ち上げを end の整合条件で束ねる。
規約：必要な形の極限の存在を仮定する。ホモトピー群と極限の交換は含まない。
使われ方：Goerss–Jardine VIII §1。骨格の end の塔の通常の極限の計算。
-/

@[expose] public section

universe u v w z a b

open CategoryTheory CategoryTheory.Limits Opposite

namespace SerrePositivity.KST.Spectra.EndLimitPreservation

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C : Type u} [Category.{v} C] {J : Type w} [Category.{z} J]
  {K : Type a} [Category.{b} K] [HasLimitsOfShape K C]
  [∀ (D : Jᵒᵖ ⥤ J ⥤ C), HasEnd D]

abbrev evaluationPair (i j : J) : (Jᵒᵖ ⥤ J ⥤ C) ⥤ C :=
  (evaluation Jᵒᵖ (J ⥤ C)).obj (op i) ⋙ (evaluation J C).obj j

variable {F : K ⥤ (Jᵒᵖ ⥤ J ⥤ C)} {c : Cone F} (hc : IsLimit c)

def componentCone (s : Cone (F ⋙ endFunctor J C)) (j : J) :
    Cone (F ⋙ evaluationPair j j) where
  pt := s.pt
  π := {
    app k := s.π.app k ≫ end_.π (F.obj k) j
    naturality k l f := by
      change 𝟙 _ ≫ (s.π.app l ≫ end_.π (F.obj l) j) =
        (s.π.app k ≫ end_.π (F.obj k) j) ≫ ((F.map f).app (op j)).app j
      have h := congrArg (fun t ↦ t ≫ end_.π (F.obj l) j) (s.w f)
      simpa only [Category.id_comp, Category.assoc, Functor.comp_map,
        endFunctor_map, end_.map_π] using h.symm }

def componentLift (s : Cone (F ⋙ endFunctor J C)) (j : J) :
    s.pt ⟶ (c.pt.obj (op j)).obj j :=
  (isLimitOfPreserves (evaluationPair j j) hc).lift (componentCone s j)

@[reassoc]
lemma componentLift_π (s : Cone (F ⋙ endFunctor J C)) (j : J) (k : K) :
    componentLift hc s j ≫ ((c.π.app k).app (op j)).app j =
      s.π.app k ≫ end_.π (F.obj k) j :=
  (isLimitOfPreserves (evaluationPair j j) hc).fac (componentCone s j) k

lemma componentLift_condition (s : Cone (F ⋙ endFunctor J C)) {i j : J} (f : i ⟶ j) :
    componentLift hc s i ≫ (c.pt.obj (op i)).map f =
      componentLift hc s j ≫ (c.pt.map f.op).app j := by
  apply (isLimitOfPreserves (evaluationPair i j) hc).hom_ext
  intro k
  change (componentLift hc s i ≫ (c.pt.obj (op i)).map f) ≫
      ((c.π.app k).app (op i)).app j =
    (componentLift hc s j ≫ (c.pt.map f.op).app j) ≫
      ((c.π.app k).app (op i)).app j
  have hi := ((c.π.app k).app (op i)).naturality f
  change (c.pt.obj (op i)).map f ≫ ((c.π.app k).app (op i)).app j =
    ((c.π.app k).app (op i)).app i ≫ ((F.obj k).obj (op i)).map f at hi
  have hj := NatTrans.congr_app ((c.π.app k).naturality f.op) j
  change (c.pt.map f.op).app j ≫ ((c.π.app k).app (op i)).app j =
    ((c.π.app k).app (op j)).app j ≫ ((F.obj k).map f.op).app j at hj
  simp only [Category.assoc]
  rw [hi, hj]
  simp only [← Category.assoc, componentLift_π]
  simp only [Category.assoc]
  exact congrArg (fun t ↦ s.π.app k ≫ t) (end_.condition (F.obj k) f)

/-- 概要：end を施した極限錐は極限錐である。
方針：成分の極限の普遍性から end の持ち上げを作り、一意性も成分で検査する。
規約：任意の添字圏 K の通常の極限。
使われ方：Goerss–Jardine VIII §1。複数の通常の極限の順序の交換。 -/
def isLimit : IsLimit ((endFunctor J C).mapCone c) where
  lift s := end_.lift (componentLift hc s) (fun _ _ f ↦ componentLift_condition hc s f)
  fac s k := by
    apply end_.hom_ext
    intro j
    change (end_.lift _ _ ≫ end_.map (c.π.app k)) ≫ end_.π (F.obj k) j =
      s.π.app k ≫ end_.π (F.obj k) j
    rw [Category.assoc, end_.map_π, ← Category.assoc, end_.lift_π, componentLift_π]
  uniq s m hm := by
    apply end_.hom_ext
    intro j
    rw [end_.lift_π]
    apply (isLimitOfPreserves (evaluationPair j j) hc).hom_ext
    intro k
    change (m ≫ end_.π c.pt j) ≫ ((c.π.app k).app (op j)).app j =
      componentLift hc s j ≫ ((c.π.app k).app (op j)).app j
    rw [componentLift_π, Category.assoc, ← end_.map_π, ← Category.assoc]
    exact congrArg (fun t ↦ t ≫ end_.π (F.obj k) j) (hm k)

instance preservesLimit : PreservesLimit F (endFunctor J C) :=
  ⟨fun h ↦ ⟨isLimit h⟩⟩

end

end SerrePositivity.KST.Spectra.EndLimitPreservation
