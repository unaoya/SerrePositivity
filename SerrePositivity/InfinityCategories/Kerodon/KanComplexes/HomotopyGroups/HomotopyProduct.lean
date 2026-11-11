module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyInvariance

/-!
概要：直積の正次数ホモトピー類を二つの射影の像から識別する。
方針：同じ位置の RelStruct の二つの充填を直積へ組み合わせる。
規約：Kan 性は商と誘導群準同型にのみ使う。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。loop の積の高次群での計算。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.KanHomotopyGroup
end SerrePositivity.KST.Spectra.KanHomotopyGroup
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : SSet.{u}} {x : X _⦋0⦌} {y : Y _⦋0⦌} {n : ℕ}

/-- 概要：Kan 複体の直積は Kan。
方針：ホーンの二つの射影をそれぞれ充填し、直積へ組み合わせる。
規約：通常の単体集合の直積を使う。
使われ方：Goerss–Jardine I §7、Kerodon §3.1（Tag 00SZ）。直積上のホモトピー類。 -/
instance prod_kanComplex [KanComplex X] [KanComplex Y] : KanComplex (X ⊗ Y) := by
  rw [KanComplex.iff]
  intro n i fs hf
  obtain ⟨a, ha⟩ := KanComplex.hornFilling (hf.desc ≫ fst X Y)
  obtain ⟨b, hb⟩ := KanComplex.hornFilling (hf.desc ≫ snd X Y)
  have h : (horn (n + 1) i).ι ≫ lift a b = hf.desc := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [Category.assoc, lift_fst, lift_snd, ha, hb]
  refine ⟨lift a b, fun j hj => ?_⟩
  rw [← horn.ι_ι_assoc i j hj, h]
  exact hf.ι_desc j hj

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup export _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups (prod_kanComplex)


/-- 概要：二つの射影に沿う RelStruct を直積の RelStruct へまとめる。
方針：充填単体を直積の lift で組にし、各面を射影で検査する。
規約：両方の充填の面添字は同じ i。
使われ方：Goerss–Jardine I §7。直積上のホモトピー類の識別。 -/
def prodRelStruct {f g : (X ⊗ Y).PtSimplex n (x, y)} {i : Fin (n + 1)}
    (r : PtSimplex.RelStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (fst X Y) rfl f)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (fst X Y) rfl g) i)
    (s : PtSimplex.RelStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (snd X Y) rfl f)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (snd X Y) rfl g) i) : PtSimplex.RelStruct f g i where
  map := lift r.map s.map
  δ_castSucc_map := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [Category.assoc, lift_fst, lift_snd,
        PtSimplex.RelStruct.δ_castSucc_map, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex_map]
  δ_succ_map := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [Category.assoc, lift_fst, lift_snd,
        PtSimplex.RelStruct.δ_succ_map, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex_map]
  δ_map_of_lt j hj := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [Category.assoc, lift_fst, lift_snd,
        r.δ_map_of_lt j hj, s.δ_map_of_lt j hj, SSet.const_comp]
  δ_map_of_gt j hj := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [Category.assoc, lift_fst, lift_snd,
        r.δ_map_of_gt j hj, s.δ_map_of_gt j hj, SSet.const_comp]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup export _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups (prodRelStruct)


/-- 概要：直積のホモトピー類は二つの射影の像で決まる。
方針：同じ添字の関係充填を取り、二つの充填を直積にする。
規約：次数は n+1、基点は (x,y)。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。積の高次群の分解。 -/
theorem prod_map_injective [KanComplex X] [KanComplex Y] (n : ℕ)
    (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    Function.Injective
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := n) (fst X Y) (x := (x, y)) rfl).prod
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := n) (snd X Y) (x := (x, y)) rfl)) := by
  intro a b h
  induction a using Quotient.inductionOn with | h f => ?_
  induction b using Quotient.inductionOn with | h g => ?_
  have hx : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (fst X Y) rfl f) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (fst X Y) rfl g) :=
    congrArg Prod.fst h
  have hy : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (snd X Y) rfl f) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (snd X Y) rfl g) :=
    congrArg Prod.snd h
  obtain ⟨r⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexRel_iff_relStruct 0).mp ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk_eq_iff _ _).mp hx)
  obtain ⟨s⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexRel_iff_relStruct 0).mp ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk_eq_iff _ _).mp hy)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.sound (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.prodRelStruct r s)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup export _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups (prod_map_injective)


end

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.prodRelStruct (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.prodRelStruct := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.prodRelStruct

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.prod_kanComplex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.prod_kanComplex := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.prod_kanComplex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.prod_map_injective := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.prod_map_injective

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.prodRelStruct._proof_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.prodRelStruct._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.prodRelStruct._proof_2 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.prodRelStruct._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.prodRelStruct._proof_3 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.prodRelStruct._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.prodRelStruct._proof_4 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.prodRelStruct._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.prodRelStruct._proof_5 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.prodRelStruct._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.KanHomotopyGroup.prodRelStruct._proof_6 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.prodRelStruct._proof_6
