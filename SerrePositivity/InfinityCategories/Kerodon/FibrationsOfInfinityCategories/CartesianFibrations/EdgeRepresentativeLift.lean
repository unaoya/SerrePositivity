module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpacePiZero

/-!
概要：inner 射の下で像の辺を指定し、元のホモトピー圏の射の類を保って代表を直す。
方針：像の同じ類を右写像空間の辺で結び、一次ホーンを終点固定で持ち上げる。
規約：両端と像の代表は厳密に固定する。
使われ方：底で恒等な相対 Kan 単位の代表の構成。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：同じ射の類を持つ二辺は右写像空間内の辺で結べる。
方針：二つのホモトピー圏の比較から右ホモトピーの三角形を得る。
規約：得る辺の向きは後の代表 g から前の代表 f。
使われ方：像の代表を修正するための一次ホーンの底の辺。 -/
lemma exists_kanPinchedHomEdge_of_homMk_eq {X : SSet.{u}} [Quasicategory X]
    {x y : X _⦋0⦌} (f g : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (h : SSet.Truncated.HomotopyCategory.homMk f = SSet.Truncated.HomotopyCategory.homMk g) :
    Nonempty (SSet.Edge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv x y).symm g) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv x y).symm f)) := by
  have h₂ : SSet.Truncated.HomotopyCategory₂.homMk f =
      SSet.Truncated.HomotopyCategory₂.homMk g := by
    have hh := congrArg (fun m ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory ((truncation 2).obj X)).map m) h
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory,
      SSet.Truncated.HomotopyCategory.lift_map_homMk] using hh
  have hh : SSet.Truncated.HomotopicL f g := Quotient.exact h₂
  obtain ⟨tri⟩ := SSet.Truncated.HomotopicL.homotopicR hh
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomEdgeOfRightHomotopy tri⟩

/-- 概要：inner 射の右写像空間の辺は指定された終点から持ち上がる。
方針：一次の最後のホーンへ定数頂点を置き、全ホーン持ち上げを使う。
規約：持ち上げた辺の像を指定された辺そのものに等しくする。
使われ方：元の辺の類を保つ代表修正。 -/
lemma exists_kanPinchedHomEdge_lift_target {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (p : X ⟶ Y) [InnerFibration p]
    (x y : X _⦋0⦌) (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) _⦋0⦌)
    {w : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (p.app (Opposite.op ⦋0⦌) x) (p.app (Opposite.op ⦋0⦌) y)) _⦋0⦌}
    (e : SSet.Edge w ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap p x y).app (Opposite.op ⦋0⦌) v)) :
    ∃ L : (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y,
      stdSimplex.δ 0 ≫ L = SSet.yonedaEquiv.symm v ∧
      L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap p x y = SSet.yonedaEquiv.symm e.edge := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomMap_hasLiftingProperty_horn p x y 0 (1 : Fin 2)
  let sq : CommSq (SSet.const v) (horn 1 1).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap p x y)
      (SSet.yonedaEquiv.symm e.edge) := by
    constructor
    apply horn.hom_ext'
    intro j hj
    fin_cases j
    · rw [SSet.const_comp, SSet.comp_const, horn.ι_ι_assoc,
        stdSimplex.δ_comp_yonedaEquiv_symm]
      exact (SSet.yonedaEquiv_symm_zero _).symm.trans
        (congrArg SSet.yonedaEquiv.symm e.tgt_eq.symm)
    · exact (hj rfl).elim
  refine ⟨sq.lift, ?_, sq.fac_right⟩
  rw [← horn.ι_ι_assoc 1 0 (by decide), sq.fac_left, SSet.comp_const,
    SSet.yonedaEquiv_symm_zero]

/-- 概要：像の射の類を保つ指定代表へ、元の辺の類を変えずに持ち上げられる。
方針：像の二代表を写像空間の辺で結び、既知の終点から持ち上げた始点を取る。
規約：辺 f の両端と像の代表 g を同時に固定する。
使われ方：U 像の類が恒等な単位を底で厳密に定値な代表へ直す。 -/
lemma exists_kanEdgeRepresentative_lift {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (p : X ⟶ Y) [InnerFibration p]
    {x y : X _⦋0⦌} (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (g : SSet.Truncated.Edge (X := (truncation 2).obj Y)
      (p.app (Opposite.op ⦋0⦌) x) (p.app (Opposite.op ⦋0⦌) y))
    (h : SSet.Truncated.HomotopyCategory.homMk (f.map ((truncation 2).map p)) =
      SSet.Truncated.HomotopyCategory.homMk g) :
    ∃ f' : SSet.Truncated.Edge (X := (truncation 2).obj X) x y,
      (f'.map ((truncation 2).map p)).edge = g.edge ∧
      SSet.Truncated.HomotopyCategory.homMk f' = SSet.Truncated.HomotopyCategory.homMk f := by
  let v := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv x y).symm f
  obtain ⟨e⟩ := exists_kanPinchedHomEdge_of_homMk_eq (f.map ((truncation 2).map p)) g h
  have hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap p x y).app (Opposite.op ⦋0⦌) v =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv _ _).symm (f.map ((truncation 2).map p)) := by rfl
  rw [← hv] at e
  obtain ⟨L, hL₁, hLp⟩ := exists_kanPinchedHomEdge_lift_target p x y v e
  let s := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y).δ 1 (SSet.yonedaEquiv L)
  have ht : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y).δ 0 (SSet.yonedaEquiv L) = v := by
    have ht := congrArg SSet.yonedaEquiv hL₁
    simpa only [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply] using ht
  have hs : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap p x y).app (Opposite.op ⦋0⦌) s =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv _ _).symm g := by
    have hs := congrArg (fun k ↦ stdSimplex.δ (1 : Fin 2) ≫ k) hLp
    rw [← Category.assoc, stdSimplex.δ_comp_yonedaEquiv_symm] at hs
    have hs' := congrArg SSet.yonedaEquiv hs
    rw [SSet.yonedaEquiv_comp, stdSimplex.yonedaEquiv_δ_comp,
      Equiv.apply_symm_apply] at hs'
    exact hs'.trans e.src_eq
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv x y s, ?_, ?_⟩
  · exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.val hs
  · have he := SSet.π₀.sound (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv L)))
    have hh := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomPiZeroToHom x y) he
    change SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv x y s) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv x y
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y).δ 0 (SSet.yonedaEquiv L))) at hh
    rw [ht, Equiv.apply_symm_apply] at hh
    exact hh

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
