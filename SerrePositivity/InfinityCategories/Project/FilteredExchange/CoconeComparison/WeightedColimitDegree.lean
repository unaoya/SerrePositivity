module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.WeightedCones.WeightedColimit

/-!
概要：単体集合の重み付き coend の各次数での普遍性。
方針：評価関手による colimit の保存を二変数図式の cowedge に移す。
規約：次数ごとの集合の射には単体方向の自然性を要求しない。
使われ方：Bousfield–Kan 比較射の各成分の全単射の証明。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {I : Type u} [SmallCategory I]

/-- 概要：重み付き coend の二変数図式を一つの次数で評価する。
方針：各係数と重みの積を集合として取る。
規約：値の宇宙は元の単体集合と同じ。使われ方：集合の coend の普遍性。 -/
def weightedColimitDegreeDiagram (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u})
    (d : SimplexCategoryᵒᵖ) : Iᵒᵖ ⥤ I ⥤ Type u :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitDiagram W F ⋙
    (Functor.whiskeringRight I SSet.{u} (Type u)).obj ((evaluation _ _).obj d)

/-- 概要：coend の各普遍脚を次数 d で評価した cowedge。
方針：元の dinaturality を評価する。
規約：頂点は元の coend の d 単体。使われ方：次数ごとの降下。 -/
def weightedColimitDegreeCowedge (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u})
    (d : SimplexCategoryᵒᵖ) : Cowedge (weightedColimitDegreeDiagram W F d) :=
  Cowedge.mk ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F).obj d) (fun i ↦ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι W F i).app d) (by
    intro i j f
    exact congrArg (fun t ↦ t.app d) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit_condition W F f))

/-- 概要：元の coend の各次数は評価した二変数図式の coend。
方針：評価による multicoequalizer の保存と厳密な図式比較を使う。
規約：filtered 性は不要。使われ方：次数ごとの逆を coend から降下させる。 -/
def weightedColimitDegreeCowedge_isColimit (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u})
    (d : SimplexCategoryᵒᵖ) : IsColimit (weightedColimitDegreeCowedge W F d) := by
  let E : SSet.{u} ⥤ Type u := (evaluation _ _).obj d
  have h := isColimitOfPreserves E
    (colimit.isColimit (multispanIndexCoend (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitDiagram W F)).multispan)
  let e : (multispanIndexCoend (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitDiagram W F)).multispan ⋙ E ≅
      (multispanIndexCoend (weightedColimitDegreeDiagram W F d)).multispan :=
    NatIso.ofComponents (fun j ↦ by cases j <;> exact Iso.refl _) (by
      rintro (_ | _) (_ | _) (_ | _ | _) <;> rfl)
  apply (IsColimit.precomposeHomEquiv e (weightedColimitDegreeCowedge W F d)).toFun
  apply IsColimit.ofIsoColimit h
  refine Cocone.ext (Iso.refl _) ?_
  intro j
  cases j <;>
    simp [weightedColimitDegreeCowedge, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι, coend.ι, e,
      weightedColimitDegreeDiagram, E]

variable (W : Iᵒᵖ ⥤ SSet.{u}) (F : I ⥤ SSet.{u}) (d : SimplexCategoryᵒᵖ)
  {T : Type u} (s : ∀ i, (F.obj i ⊗ W.obj (Opposite.op i)).obj d → T)
  (hs : ∀ {i j} (f : i ⟶ j) (x : (F.obj i).obj d) (w : (W.obj (Opposite.op j)).obj d),
    s i (x, (W.map f.op).app d w) = s j ((F.map f).app d x, w))

/-- 概要：各次数で dinatural な集合の写像を元の coend の単体から降下させる。
方針：評価した cowedge の余極限性を使う。
規約：単体方向の自然性はここでは不要。使われ方：比較射の次数ごとの逆。 -/
def weightedColimitDegreeDesc : (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimit W F).obj d → T :=
  Cowedge.IsColimit.desc (weightedColimitDegreeCowedge_isColimit W F d)
    (fun i ↦ ↾(s i)) (by
      intro i j f
      apply ConcreteCategory.hom_ext
      rintro ⟨x, w⟩
      exact hs f x w)

/-- 概要：次数ごとの降下は各生成元上で指定された写像。
方針：cowedge の降下の計算則を評価する。
規約：重みの全ての単体を含む。使われ方：両逆則の検証。 -/
lemma weightedColimitDegreeDesc_ι (i : I)
    (x : (F.obj i ⊗ W.obj (Opposite.op i)).obj d) :
    weightedColimitDegreeDesc W F d s hs ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.weightedColimitι W F i).app d x) = s i x := by
  have hd := Cowedge.IsColimit.π_desc (weightedColimitDegreeCowedge_isColimit W F d)
    (fun i ↦ ↾(s i)) (by
      intro j k f
      apply ConcreteCategory.hom_ext
      rintro ⟨y, w⟩
      exact hs f y w) i
  exact congrArg (fun t ↦ (ConcreteCategory.hom t) x) hd

end SerrePositivity.InfinityCategories.Project.FilteredExchange
