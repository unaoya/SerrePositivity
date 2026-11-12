module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberComparisonInvertible
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IdentityCofiber
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroCofiberIso

/-! # 同型射の cofiber の消滅

概要：同型射の cofiber は零であり、安定な場合には零 cofiber による同型判定が同値となる。
方針：恒等射の列四角形との比較の最初の二成分を同型に取り、全体を可逆にする。
規約：cofiber の選択は任意。使われ方：比較射の cofiber による同型判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：cofiber 列の第一射が同型なら第三対象は零である。
方針：第二対象から零角への辺を二列に並べた恒等射の cofiber と可逆に比較する。
規約：値域は quasicategory、安定性は不要。使われ方：零 cofiber による同型判定の逆向き。 -/
lemma ZeroTriangle.zero_cofiber_of_isIso_bottom {X : SSet.{u}} [Quasicategory X]
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) (hi : IsIso (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoBottom t.square)) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 1 1) := by
  let : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X := ⟨⟨_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 1, t.zero_corner⟩⟩
  let g := Classical.choice (t.zero_corner.2.nonempty_edge (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 1 0))
  let q : (Δ[1] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm g.edge
  have hq : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram q = q := by
    simp [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge]
  have hB : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram q) 0 0 = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 1 0 := by
    have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_source (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram q)
    change X.δ 1 (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram q)) = _ at h
    rw [hq] at h
    exact h.symm.trans
      ((congrArg (X.δ 1) (SSet.yonedaEquiv.apply_symm_apply g.edge)).trans g.src_eq)
  have hZ : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram q) 0 1 = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 1 := by
    have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareRightEdge_target (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram q)
    change X.δ 0 (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram q)) = _ at h
    rw [hq] at h
    exact h.symm.trans
      ((congrArg (X.δ 0) (SSet.yonedaEquiv.apply_symm_apply g.edge)).trans g.tgt_eq)
  have hzq : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (q.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram q) 0 1)
    rw [hZ]
    exact t.zero_corner
  let d := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.columnZeroTriangle q hzq
  let a : SSet.Truncated.Edge (X := (truncation 2).obj X)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex d.square 0 0) :=
    { edge := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow t.square).edge
      src_eq := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow t.square).src_eq
      tgt_eq := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow t.square).tgt_eq.trans hB.symm }
  let b : SSet.Truncated.Edge (X := (truncation 2).obj X)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 1 0) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex d.square 1 0) :=
    { edge := (SSet.Truncated.Edge.id (X := (truncation 2).obj X)
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 1 0)).edge
      src_eq := (SSet.Truncated.Edge.id (X := (truncation 2).obj X)
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 1 0)).src_eq
      tgt_eq := (SSet.Truncated.Edge.id (X := (truncation 2).obj X)
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 1 0)).tgt_eq.trans hB.symm }
  have ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge a :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow t.square) (f := a) rfl).1 hi
  have hb₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (SSet.Truncated.Edge.id (X := (truncation 2).obj X)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 1 0)) := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk (SSet.Truncated.Edge.id _))
    rw [SSet.Truncated.HomotopyCategory.homMk_id]
    infer_instance
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge b := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := SSet.Truncated.Edge.id (X := (truncation 2).obj X)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 1 0)) (f := b) rfl).1 hb₀
  let c := SSet.Truncated.Edge.CompStruct.compId (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow t.square)
  have hc : (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow t.square).CompStruct b a :=
    { simplex := c.simplex, d₂ := c.d₂, d₀ := c.d₀, d₁ := c.d₁ }
  have hid : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoBottom d.square = 𝟙 (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex d.square 0 0) :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.columnZeroTriangle_f_eq_id q hzq
  have hcomm : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoBottom t.square ≫ SSet.Truncated.HomotopyCategory.homMk b =
      SSet.Truncated.HomotopyCategory.homMk a ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoBottom d.square := by
    calc
      _ = SSet.Truncated.HomotopyCategory.homMk a :=
        SSet.Truncated.HomotopyCategory.homMk_comp_homMk hc
      _ = _ := by
        rw [hid]
        exact (Category.comp_id (obj := hoFunctor.obj X)
          (SSet.Truncated.HomotopyCategory.homMk a)).symm
  obtain ⟨Q, _, _, hQ⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_invertibleCofiberSquareHomotopy_of_comm t d ht
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.columnZeroTriangle_isCofiber q hzq) a b ha hb hcomm
  let e := asIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy Q))
  let v : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) _⦋0⦌ :=
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2))
  let E := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) v
  have hd : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (E.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d.square)) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
    exact hzq
  have hzero := hd.of_vertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e E).symm
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex] at hzero
  exact hzero

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroTriangle (zero_cofiber_of_isIso_bottom)


/-- 概要：指定された同型辺の任意の cofiber は零である。
方針：辺と cofiber 列の第一射の Arrow の等号で同型性を移す。
規約：安定性は不要。使われ方：選択に依らない cofiber の消滅。 -/
lemma CofiberSquare.zero_of_homMk_isIso {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} {f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    (s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare f) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge f) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex s.cofiber := by
  let : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X := ⟨⟨_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex s.square 0 1, s.zero_corner⟩⟩
  have hs : IsIso s.toZeroTriangle.hoShortComplex.f :=
    (congrArg (fun a : Arrow (hoFunctor.obj X) => IsIso a.hom) s.hoShortComplex_f_arrow).mpr hi
  exact s.toZeroTriangle.zero_cofiber_of_isIso_bottom s.isPushout hs

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberSquare (zero_of_homMk_isIso)


/-- 概要：安定な場合、指定辺が同型であることと任意の選んだ cofiber が零であることは同値。
方針：同型からの消滅と、零 cofiber からの同型判定を組み合わせる。
規約：cofiber 四角形の選択は固定してもよい。使われ方：比較射の同型判定。 -/
lemma CofiberSquare.homMk_isIso_iff_zero {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {x y : X _⦋0⦌} {f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    (s : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare f) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge f ↔ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex s.cofiber :=
  ⟨s.zero_of_homMk_isIso, s.homMk_isIso_of_zero⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare export _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberSquare (homMk_isIso_iff_zero)


end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
