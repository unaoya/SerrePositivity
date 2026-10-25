module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.FixedSourceCocone
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.ThinNerveMapExt

/-!
概要：固定入力図式を含む相対前置図式を同じ成分表示へ因子化する。
方針：固定入力と前置形状の join を展開し、指定成分を右因子に含める。
規約：入力の全単体を保持し、入力の余極限は要求しない。
使われ方：小さい入力図式を伴う相対交互塔の一段選択。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：固定入力付き前置図式を小さい join の宇宙持ち上げ上で読む。
方針：既存の join 宇宙同型で全 uncurry を前合成する。
規約：固定入力と全前置図式を変更しない。
使われ方：元の Ind 表示の相対因子化への入力。 -/
def fixedSourceShapeDiagram {K L : SSet.{u}} {Y : SSet.{u + 1}}
    {z : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ Y}
    (R : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶ sliceUnder z) :
    (SSet.uliftFunctor.{u + 1, u}).obj (join K L) ⟶ Y :=
  (uliftJoinIso K L).hom ≫ sliceUnderUncurry R

/-- 概要：展開した全前置図式の左境界は固定入力図式。
方針：join 宇宙同型の左包含と coslice の固定条件を使う。
規約：元の全入力図式の等式。
使われ方：入力頂点の compact 性の回収。 -/
lemma fixedSourceShapeDiagram_inl {K L : SSet.{u}} {Y : SSet.{u + 1}}
    {z : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ Y}
    (R : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶ sliceUnder z) :
    (SSet.uliftFunctor.{u + 1, u}).map (joinInl K L) ≫ fixedSourceShapeDiagram R = z := by
  rw [fixedSourceShapeDiagram, ← Category.assoc, uliftJoinIso_inl, sliceUnderUncurry_fixed]

/-- 概要：展開した全前置図式の右境界は元の前置図式の射影。
方針：join 宇宙同型の右包含と coslice 射影を使う。
規約：元の全前置図式の等式。
使われ方：既存成分表示との一致。 -/
lemma fixedSourceShapeDiagram_inr {K L : SSet.{u}} {Y : SSet.{u + 1}}
    {z : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ Y}
    (R : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶ sliceUnder z) :
    (SSet.uliftFunctor.{u + 1, u}).map (joinInr K L) ≫ fixedSourceShapeDiagram R =
      R ≫ sliceUnderProjection z := by
  rw [fixedSourceShapeDiagram, ← Category.assoc, uliftJoinIso_inr, sliceUnderUncurry_projection]

/-- 概要：単射の宇宙持ち上げも単射。
方針：各次数で ULift.down を適用して元の単射へ戻す。
規約：元の全単体写像を保持する。
使われ方：相対因子化の成分包含の単射性。 -/
lemma mono_uliftMap {K L : SSet.{u}} (f : K ⟶ L) [Mono f] :
    Mono ((SSet.uliftFunctor.{u + 1, u}).map f) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  apply (mono_iff_injective _).2
  rintro ⟨v⟩ ⟨w⟩ h
  apply ULift.ext
  have hm : Mono (f.app n) := (NatTrans.mono_iff_mono_app _).mp inferInstance n
  exact (mono_iff_injective _).mp hm (congrArg ULift.down h)

/-- 概要：固定入力付き全前置図式は、両境界の compact 性から頂点ごとに compact。
方針：join の各頂点を元の左右どちらかの頂点へ戻す。
規約：入力図式の余極限や compact 余錐を要求しない。
使われ方：元の Ind 表示の相対因子化。 -/
lemma fixedSourceShapeDiagram_vertex_compact
    {μ : Cardinal.{u}} {K L : SSet.{u}} {B : SSet.{u + 1}} [Quasicategory B]
    {x : (Δ[0] : SSet.{u + 1}) ⟶ B}
    {z : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ sliceOver x}
    (R : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶ sliceUnder z)
    (hz : ∀ v : K _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ
      ((z ≫ sliceOverProjection x).app (Opposite.op ⦋0⦌) (ULift.up v)))
    (hR : ∀ v : L _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ
      ((R ≫ sliceUnderProjection z ≫ sliceOverProjection x).app
        (Opposite.op ⦋0⦌) (ULift.up v))) :
    ∀ v : (join K L) _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ
      ((fixedSourceShapeDiagram R ≫ sliceOverProjection x).app
        (Opposite.op ⦋0⦌) (ULift.up v)) := by
  intro v
  rcases join_vertex_cases v with ⟨w, rfl⟩ | ⟨w, rfl⟩
  · have h := congrArg (fun f ↦ (f ≫ sliceOverProjection x).app (Opposite.op ⦋0⦌)
        (ULift.up w)) (fixedSourceShapeDiagram_inl R)
    exact h.symm ▸ hz w
  · have h := congrArg (fun f ↦ (f ≫ sliceOverProjection x).app (Opposite.op ⦋0⦌)
        (ULift.up w)) (fixedSourceShapeDiagram_inr R)
    exact h.symm ▸ hR w

/-- 概要：固定入力付き全前置図式を元の成分表示内へ相対因子化できる。
方針：全 join 図式の小ささと compact 性を一般相対因子化へ渡す。
規約：元の入力図式と指定成分の全前置表示を保持する。
使われ方：小図式を固定する相対交互構成の一段選択。 -/
lemma exists_fixedSourceFactorization
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {A : SSet.{u}} [Quasicategory A]
    {J K L I : SSet.{u}} [Quasicategory J] [Quasicategory K]
    [Quasicategory L] [Quasicategory I] [IsKappaFiltered μ I]
    (hJ : IsKappaSmall μ J) (hK : IsKappaSmall μ K) (hL : IsKappaSmall μ L)
    {x : (Δ[0] : SSet.{u + 1}) ⟶ Ind.IndInfinity μ A}
    {z : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ sliceOver x}
    (R : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶ sliceUnder z)
    (a : J ⟶ I) (j : J ⟶ L) [Mono j]
    (P : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ sliceOver x)
    (hz : ∀ v : K _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ
      ((z ≫ sliceOverProjection x).app (Opposite.op ⦋0⦌) (ULift.up v)))
    (hR : ∀ v : L _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ
      ((R ≫ sliceUnderProjection z ≫ sliceOverProjection x).app
        (Opposite.op ⦋0⦌) (ULift.up v)))
    (hcol : IsColimitCone (sliceDiagramCocone P))
    (hi : (SSet.uliftFunctor.{u + 1, u}).map j ≫ R ≫ sliceUnderProjection z =
      (SSet.uliftFunctor.{u + 1, u}).map a ≫ P) :
    Nonempty (RelativeComponentFactorization a
      ((SSet.uliftFunctor.{u + 1, u}).map (j ≫ joinInr K L))
      (fixedSourceShapeDiagram R) P) := by
  have := mono_uliftMap (j ≫ joinInr K L)
  apply exists_relativeComponentFactorization hμ hJ
    (isKappaSmall_join (Fact.out : μ.IsRegular) hK hL) a _ _ P
    (fixedSourceShapeDiagram_vertex_compact R hz hR) hcol
  rw [CategoryTheory.Functor.map_comp, Category.assoc, fixedSourceShapeDiagram_inr]
  exact hi

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
