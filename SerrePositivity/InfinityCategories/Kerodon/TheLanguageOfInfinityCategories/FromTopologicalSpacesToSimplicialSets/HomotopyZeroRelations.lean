module


public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyIndexing
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：Kan 複体の零次数で、同じ連結成分を一本の RelStruct₀ で表す。
方針：二次元の外ホーンと内ホーンを充填して対称性と推移性を証明する。
規約：零次数の群構造は要求しない。
使われ方：Kerodon Proposition 1.2.5.10（Tag 00HC）、Example 3.2.2.6（Tag 00VQ）、Theorem 3.2.6.1（Tag 00WM）。

対応節は Kerodon 1.2（Tag 0508）。
-/

@[expose] public section

universe u
open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.Spectra.ZeroRelations
end SerrePositivity.KST.Spectra.ZeroRelations
namespace SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets
open _root_.SerrePositivity.KST.Spectra

namespace ZeroRelations
open _root_.SerrePositivity.KST.Spectra.ZeroRelations

variable {X : SSet.{u}} [KanComplex X] {x : X _⦋0⦌}
  {f g h : X.PtSimplex 0 x}

/-- 概要：零次数の RelStruct₀ は対称である。
方針：元の辺と始点の定数辺を外ホーンへ貼り、欠けた逆向きの辺を取る。
規約：定数辺の頂点は g の頂点。
使われ方：Kerodon Proposition 1.2.5.10（Tag 00HC）。零次数の関係の同値性。 -/
noncomputable def symm (r : PtSimplex.RelStruct₀ f g) : PtSimplex.RelStruct₀ g f := by
  let u : (Δ[1] : SSet.{u}) ⟶ X := SSet.const (PtSimplex.equiv₀ x g)
  have hglue : stdSimplex.δ (1 : Fin 2) ≫ r.map = stdSimplex.δ (1 : Fin 2) ≫ u := by
    change stdSimplex.δ (0 : Fin 1).succ ≫ r.map = _
    rw [r.δ_succ_map, comp_const]
    exact g.map_eq_const_equiv₀
  let q := horn₂₀.isPushout.desc r.map u hglue
  let φ := (KanComplex.hornFilling q).choose
  have hφ := (KanComplex.hornFilling q).choose_spec
  have h₂ : stdSimplex.δ (2 : Fin 3) ≫ φ = r.map := by
    rw [← horn.ι_ι_assoc (0 : Fin 3) (2 : Fin 3) (by decide), ← hφ]
    exact horn₂₀.isPushout.inl_desc _ _ _
  have h₁ : stdSimplex.δ (1 : Fin 3) ≫ φ = u := by
    rw [← horn.ι_ι_assoc (0 : Fin 3) (1 : Fin 3) (by decide), ← hφ]
    exact horn₂₀.isPushout.inr_desc _ _ _
  refine {
    map := stdSimplex.δ (0 : Fin 3) ≫ φ
    δ_castSucc_map := ?_
    δ_succ_map := ?_
    δ_map_of_lt := ?_
    δ_map_of_gt := ?_ }
  · change stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) ≫ φ = g.map
    have hd : stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) =
        stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) :=
      stdSimplex.δ_comp_δ_self (i := (0 : Fin 2))
    rw [← Category.assoc, hd, Category.assoc, h₁, comp_const]
    exact g.map_eq_const_equiv₀.symm
  · change stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) ≫ φ = f.map
    have hd : stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) =
        stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) :=
      (stdSimplex.δ_comp_δ (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)).symm
    rw [← Category.assoc, hd, Category.assoc, h₂]
    exact r.δ_castSucc_map
  · intro j hj; exact (Fin.not_lt_zero j hj).elim
  · intro j hj; exact (not_lt_of_ge (Fin.le_last j) hj).elim

/-- 概要：零次数の RelStruct₀ は推移的である。
方針：二本の辺を内ホーンに貼り、欠けた合成辺を取る。
規約：r と r' の共通の端点は g。
使われ方：Kerodon Proposition 1.2.5.10（Tag 00HC）。零次数の関係の同値性。 -/
noncomputable def trans (r : PtSimplex.RelStruct₀ f g) (r' : PtSimplex.RelStruct₀ g h) :
    PtSimplex.RelStruct₀ f h := by
  have hglue : stdSimplex.δ (0 : Fin 2) ≫ r'.map = stdSimplex.δ (1 : Fin 2) ≫ r.map := by
    change stdSimplex.δ (0 : Fin 1).castSucc ≫ r'.map =
      stdSimplex.δ (0 : Fin 1).succ ≫ r.map
    rw [r'.δ_castSucc_map, r.δ_succ_map]
  let q := horn₂₁.isPushout.desc r'.map r.map hglue
  let φ := (KanComplex.hornFilling q).choose
  have hφ := (KanComplex.hornFilling q).choose_spec
  have h₂ : stdSimplex.δ (2 : Fin 3) ≫ φ = r'.map := by
    rw [← horn.ι_ι_assoc (1 : Fin 3) (2 : Fin 3) (by decide), ← hφ]
    exact horn₂₁.isPushout.inl_desc _ _ _
  have h₀ : stdSimplex.δ (0 : Fin 3) ≫ φ = r.map := by
    rw [← horn.ι_ι_assoc (1 : Fin 3) (0 : Fin 3) (by decide), ← hφ]
    exact horn₂₁.isPushout.inr_desc _ _ _
  refine {
    map := stdSimplex.δ (1 : Fin 3) ≫ φ
    δ_castSucc_map := ?_
    δ_succ_map := ?_
    δ_map_of_lt := ?_
    δ_map_of_gt := ?_ }
  · change stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) ≫ φ = f.map
    have hd : stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) =
        stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) :=
      stdSimplex.δ_comp_δ (i := (0 : Fin 2)) (j := (0 : Fin 2)) (by decide)
    rw [← Category.assoc, hd, Category.assoc, h₀]
    exact r.δ_castSucc_map
  · change stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) ≫ φ = h.map
    have hd : stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (1 : Fin 3) =
        stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) :=
      stdSimplex.δ_comp_δ_self (i := (1 : Fin 2))
    rw [← Category.assoc, hd, Category.assoc, h₂]
    exact r'.δ_succ_map
  · intro j hj; exact (Fin.not_lt_zero j hj).elim
  · intro j hj; exact (not_lt_of_ge (Fin.le_last j) hj).elim

/-- 概要：Kan 複体で零次数の RelStruct₀ の存在は同値関係。
方針：退化による反射性と、ホーン充填による対称性・推移性を組み合わせる。
規約：基点 x は零単体の範囲を制限しない。
使われ方：Kerodon Proposition 1.2.5.10（Tag 00HC）。商の等式から単一の証人を得る。 -/
@[kerodon 00HC]
theorem equivalence : Equivalence (fun f g : X.PtSimplex 0 x ↦
    Nonempty (PtSimplex.RelStruct₀ f g)) :=
  ⟨fun f ↦ ⟨PtSimplex.RelStruct.refl f 0⟩,
    fun ⟨r⟩ ↦ ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.ZeroRelations.symm r⟩, fun ⟨r⟩ ⟨r'⟩ ↦ ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.ZeroRelations.trans r r'⟩⟩

end ZeroRelations

/-- 概要：Kan 複体で零次数の類の等式は RelStruct₀ の存在と同値。
方針：関係が既に同値関係であることを使い、商の同値閉包を消す。
規約：一般の単体集合では同値閉包が必要であり、ここで Kan 性を使う。
使われ方：Kerodon Example 3.2.2.6（Tag 00VQ）、Theorem 3.2.6.1（Tag 00WM）。低次数の完全性。 -/
@[kerodon 00HC]
theorem KanHomotopyZero.mk_eq_iff {X : SSet.{u}} [KanComplex X] {x : X _⦋0⦌}
    (f g : X.PtSimplex 0 x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.mk f = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.mk g ↔ Nonempty (PtSimplex.RelStruct₀ f g) := by
  change Quot.mk _ f = Quot.mk _ g ↔ _
  exact Quot.eq.trans _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.ZeroRelations.equivalence.eqvGen_iff

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero export _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopyZero (mk_eq_iff)


/-- 概要：全自然数次数で類の等式は任意の面添字の RelStruct の存在と同値。
方針：正次数の面添字独立性と零次数のホーンによる同値関係を使う。
規約：零次数の面添字は唯一の零。
使われ方：Kerodon §3.2.2（Tag 00VJ）、Theorem 3.2.6.1（Tag 00WM）。全次数の長完全列の計算。 -/
theorem KanHomotopy.mk_eq_iff_relStruct {X : SSet.{u}} [KanComplex X] {x : X _⦋0⦌}
    (n : ℕ) (f g : X.PtSimplex n x) (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk n f = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk n g ↔ Nonempty (PtSimplex.RelStruct f g i) := by
  cases n with
  | zero =>
    have hi : i = 0 := by apply Fin.ext; omega
    subst i
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopyZero.mk_eq_iff f g
  | succ n => exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk_eq_iff f g).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexRel_iff_relStruct i)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy export _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopy (mk_eq_iff_relStruct)


/-- 概要：全次数のホモトピー類は境界定数単体の代表を持つ。
方針：零次数と正次数の商への標準射の全射性を使う。
規約：n は実際の次数。
使われ方：Kerodon Construction 3.2.2.4（Tag 00VN）。零次数を含む完全性の代表への還元。 -/
theorem KanHomotopy.mk_surjective {X : SSet.{u}} [KanComplex X] {x : X _⦋0⦌} (n : ℕ) :
    Function.Surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk (X := X) (x := x) n) := by
  cases n with
  | zero => exact Quot.mk_surjective
  | succ n => exact Quotient.mk_surjective

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy export _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopy (mk_surjective)


end SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
