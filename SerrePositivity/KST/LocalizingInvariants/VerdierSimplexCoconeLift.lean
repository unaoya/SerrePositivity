module

public import SerrePositivity.KST.LocalizingInvariants.VerdierSimplexSuccessorRoof
public import SerrePositivity.KST.LocalizingInvariants.SimplexCoconeComparison

/-!
概要：商の余錐を、元の有限線型図式の分母精密化から出る実余錐へ持ち上げる。
方針：終端の実右分数とその合成二単体を、同じ終端成分の全図式比較へ貼る。
規約：元の Verdier 列のみを使い、共有経路や全図式の持ち上げを追加入力にしない。
使われ方：c5 の全有限線型図式の持ち上げにおける帰納段階。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open CartesianMonoidalCategory
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

private lemma comp_arrow_congr {T : Type*} [Category* T] {a b c a' b' c' : T}
    {f : a ⟶ b} {g : b ⟶ c} {f' : a' ⟶ b'} {g' : b' ⟶ c'}
    (hf : Arrow.mk f = Arrow.mk f') (hg : Arrow.mk g = Arrow.mk g') :
    Arrow.mk (f ≫ g) = Arrow.mk (f' ≫ g') := by
  obtain ⟨rfl, rfl, hf⟩ := (Arrow.mk_eq_mk_iff _ _).mp hf
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf
  subst f'
  obtain ⟨_, rfl, hg⟩ := (Arrow.mk_eq_mk_iff _ _).mp hg
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hg
  subst g'
  rfl

/-- 商の元の全余錐を、前段全体の分母精密化と全余錐図式の同型を保って持ち上げる。 -/
lemma exists_verdierSimplexCoconeLift_preservingPaths {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C} (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ B.obj) (z : B.obj _⦋0⦌)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (D ≫ q.hom)) (hz : d.vertex = q.hom.app (Opposite.op ⦋0⦌) z) :
    ∃ (D' : (Δ[n] : SSet.{u}) ⟶ B.obj)
      (t : Truncated.Edge (X := (truncation 2).obj ((ihom (Δ[n] : SSet.{u})).obj B.obj))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex D') (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex D)) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D'),
      t.edge ∈ (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌) ∧
      c.vertex = z ∧
      ∃ l : Truncated.Edge
        (X := (truncation 2).obj ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (c.val ≫ q.hom)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d.val),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj) l ∧
        ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj).app
          (Opposite.op ⦋1⦌) l.edge =
            ((ihom (Δ[n] : SSet.{u})).map q.hom).app (Opposite.op ⦋1⦌) t.edge ∧
        SSet.yonedaEquiv.symm l.edge ≫
          (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}) Δ[0])).app C.obj =
            curry (snd (Δ[0] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm
              (C.obj.σ 0 (q.hom.app (Opposite.op ⦋0⦌) z))) := by
  let k := SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint.{u} n)
  have hk : k = stdSimplex.obj₀Equiv.symm (Fin.last n) := Equiv.apply_symm_apply _ _
  let f₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexLeg d k
  have hfsource : (D ≫ q.hom).app (Opposite.op ⦋0⦌) k =
      q.hom.app (Opposite.op ⦋0⦌)
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) := by rw [hk]; rfl
  let f := f₀.ofEq hfsource hz
  obtain ⟨y, s, g, D', t, c, hs, ht, hv, hlast, hcz, hcg, ⟨hcomp⟩⟩ :=
    exists_verdierSimplexSuccessorRoof h D z f.toTruncated
  let cQ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (D' ≫ q.hom) := ⟨c.val ≫ q.hom, by
    rw [← Category.assoc, c.property]⟩
  have hcQz : cQ.vertex = q.hom.app (Opposite.op ⦋0⦌) z := by
    change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[n] Δ[0] ≫ c.val ≫ q.hom) = _
    rw [← Category.assoc, SSet.yonedaEquiv_comp]
    change q.hom.app (Opposite.op ⦋0⦌) c.vertex = _
    rw [hcz]
  let a : SSet.Edge (X := (ihom (Δ[n] : SSet.{u})).obj C.obj)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (D' ≫ q.hom)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (D ≫ q.hom)) :=
    SSet.Edge.ofTruncated (X := (ihom (Δ[n] : SSet.{u})).obj C.obj)
      (t.map ((truncation 2).map ((ihom (Δ[n] : SSet.{u})).map q.hom)))
  have ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge a.toTruncated := by
    change IsIso (simplexDenominatorImageIso q t ht).hom
    infer_instance
  let w := (SSet.Edge.id (q.hom.app (Opposite.op ⦋0⦌) z)).ofEq hcQz.symm hz.symm
  have hwArrow : Arrow.mk (Truncated.HomotopyCategory.homMk w.toTruncated) =
      Arrow.mk (𝟙 (HomotopyCategory.mk (q.hom.app (Opposite.op ⦋0⦌) z))) := by
    exact (Truncated.HomotopyCategory.congr_arrowMk_homMk w.toTruncated
      (SSet.Edge.id (q.hom.app (Opposite.op ⦋0⦌) z)).toTruncated rfl).trans
        (congrArg Arrow.mk (Truncated.HomotopyCategory.homMk_id _))
  have hw : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge w.toTruncated := by
    exact (congrArg (fun v : Arrow (hoFunctor.obj C.obj) => IsIso v.hom) hwArrow).mpr
      (by
        change IsIso (𝟙 (HomotopyCategory.mk (q.hom.app (Opposite.op ⦋0⦌) z) :
          hoFunctor.obj C.obj))
        infer_instance)
  have hsource : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexLeg cQ k).edge =
      (g.map ((truncation 2).map q.hom)).edge := by
    have hh : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]) ≫
        c.val ≫ q.hom = SSet.yonedaEquiv.symm g.edge ≫ q.hom := by
      simpa only [Category.assoc] using congrArg (· ≫ q.hom) hcg
    change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)))
        (𝟙 Δ[0]) ≫ (c.val ≫ q.hom)) = _
    rw [Equiv.symm_apply_apply, hh, SSet.yonedaEquiv_comp]
    exact congrArg (fun v : B.obj _⦋1⦌ => q.hom.app (Opposite.op ⦋1⦌) v)
      (SSet.yonedaEquiv.apply_symm_apply g.edge)
  have hcomponent : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgeAt a k).edge =
      (s.map ((truncation 2).map q.hom)).edge := by
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C.obj) k).app (Opposite.op ⦋1⦌)
      (((ihom (Δ[n] : SSet.{u})).map q.hom).app (Opposite.op ⦋1⦌) t.edge) =
        q.hom.app (Opposite.op ⦋1⦌) s.edge
    rw [hk]
    have hn : (ihom (Δ[n] : SSet.{u})).map q.hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C.obj) (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := B.obj) (stdSimplex.obj₀Equiv.symm (Fin.last n)) ≫ q.hom := rfl
    have hh := ConcreteCategory.congr_hom (C := Type u)
      (NatTrans.congr_app hn (Opposite.op ⦋1⦌)) t.edge
    exact hh.trans (congrArg (q.hom.app (Opposite.op ⦋1⦌)) hlast)
  have hsourceA := Truncated.HomotopyCategory.congr_arrowMk_homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexLeg cQ k).toTruncated (g.map ((truncation 2).map q.hom)) hsource
  have hcomponentA := Truncated.HomotopyCategory.congr_arrowMk_homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgeAt a k).toTruncated (s.map ((truncation 2).map q.hom)) hcomponent
  have htargetA := Truncated.HomotopyCategory.congr_arrowMk_homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexLeg d k).toTruncated f.toTruncated rfl
  have hc : Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexLeg cQ k).toTruncated ≫
        Truncated.HomotopyCategory.homMk w.toTruncated =
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorEdgeAt a k).toTruncated ≫
        Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeVertexLeg d k).toTruncated := by
    apply (Arrow.mk_inj _ _).mp
    calc
      _ = Arrow.mk (Truncated.HomotopyCategory.homMk
          (g.map ((truncation 2).map q.hom)) ≫ 𝟙 _) := comp_arrow_congr hsourceA hwArrow
      _ = Arrow.mk (Truncated.HomotopyCategory.homMk
          (g.map ((truncation 2).map q.hom))) := by rw [Category.comp_id]
      _ = Arrow.mk (Truncated.HomotopyCategory.homMk
          (s.map ((truncation 2).map q.hom)) ≫
            Truncated.HomotopyCategory.homMk f.toTruncated) :=
        congrArg Arrow.mk (Truncated.HomotopyCategory.homMk_comp_homMk hcomp).symm
      _ = _ := (comp_arrow_congr hcomponentA htargetA).symm
  obtain ⟨l, hi, hp, hv⟩ := exists_simplexCoconeComparison cQ d a w ha hw hc
  exact ⟨D', t, c, ht, hcz, l, hi, hp, hv⟩

/-- 元の入口も、二つの実経路を保持する右分数比較から従う。 -/
lemma exists_verdierSimplexCoconeLift {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C} (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ B.obj) (z : B.obj _⦋0⦌)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (D ≫ q.hom)) (hz : d.vertex = q.hom.app (Opposite.op ⦋0⦌) z) :
    ∃ (D' : (Δ[n] : SSet.{u}) ⟶ B.obj)
      (t : Truncated.Edge (X := (truncation 2).obj ((ihom (Δ[n] : SSet.{u})).obj B.obj))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex D') (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex D)) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D'),
      t.edge ∈ (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌) ∧
      c.vertex = z ∧ Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (c.val ≫ q.hom) d.val) := by
  obtain ⟨D', t, c, ht, hz, l, hi, _, _⟩ :=
    exists_verdierSimplexCoconeLift_preservingPaths h D z d hz
  have := hi
  exact ⟨D', t, c, ht, hz, ⟨asIso (Truncated.HomotopyCategory.homMk l)⟩⟩

end SerrePositivity.KST.LocalizingInvariants
