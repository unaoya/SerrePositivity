module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.RightUnitInitialCriterion

/-!
概要：固定した元の右関手に対する随伴実単位の全空間の可縮性。
方針：指定単位条件を coslice の始対象性と同定し、始対象の全部分複体で境界を充填する。
規約：全関手圏の core における高次単体を保持する。
使われ方：元の右射影のファイバーと比較する可縮な単位空間。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：始対象の頂点が張る全部分複体は非空なら可縮。
方針：正次元の境界の最初の頂点で充填し、全頂点が元の境界に属すことを使う。
規約：周囲の単体集合に充填性を仮定しない。
使われ方：固定右の普遍単位の全高次の可縮性。 -/
lemma initialVertices_isContractibleKan {X : SSet.{u}}
    (hne : ∃ x : X _⦋0⦌, IsInitialVertex x) :
    IsContractibleKan (fullSubcomplexOnVertices X IsInitialVertex : SSet.{u}) := by
  intro n b
  cases n with
  | zero =>
    obtain ⟨x, hx⟩ := hne
    let t : (fullSubcomplexOnVertices X IsInitialVertex : SSet.{u}) _⦋0⦌ := ⟨x, by
      intro v
      have hv : v = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
      simpa only [hv, op_id, CategoryTheory.Functor.map_id_apply] using hx⟩
    exact ⟨SSet.const t, boundary.hom_ext₀⟩
  | succ n =>
    let b' := b ≫ (fullSubcomplexOnVertices X IsInitialVertex).ι
    let x := SSet.yonedaEquiv (boundaryVertex n 0 ≫ b')
    have hx : IsInitialVertex x := fullSubcomplexOnVertices_vertex
      (SSet.yonedaEquiv (boundaryVertex n 0 ≫ b))
    obtain ⟨F, hF⟩ := hx n b' (SSet.yonedaEquiv.symm_apply_apply _).symm
    have hv (v : ⦋0⦌ ⟶ ⦋n + 1⦌) :
        IsInitialVertex (SSet.yonedaEquiv (SSet.stdSimplex.map v ≫ F)) := by
      have he : SSet.stdSimplex.map v =
          boundaryVertex n (v.toOrderHom 0) ≫ (boundary (n + 1)).ι := by
        rw [boundaryVertex_ι]
        apply SSet.yonedaEquiv.injective
        rw [Equiv.apply_symm_apply]
        apply SSet.stdSimplex.ext
        intro i
        fin_cases i
        rfl
      rw [he, Category.assoc, hF]
      exact fullSubcomplexOnVertices_vertex
        (SSet.yonedaEquiv (boundaryVertex n (v.toOrderHom 0) ≫ b))
    refine ⟨fullSubcomplexLiftSimplex IsInitialVertex F hv, ?_⟩
    apply (cancel_mono (fullSubcomplexOnVertices X IsInitialVertex).ι).1
    change (boundary (n + 1)).ι ≫ fullSubcomplexLiftSimplex IsInitialVertex F hv ≫
      (fullSubcomplexOnVertices X IsInitialVertex).ι = b'
    rw [fullSubcomplexLiftSimplex_ι]
    exact hF

/-- 概要：固定した元の右関手に対する随伴実単位の全部分複体。
方針：全関手圏の coslice の頂点に、同じ実単位の随伴条件を課す。
規約：左関手の保存条件は追加仮定にしない。
使われ方：元の右射影のファイバーの比較先。 -/
def RightAdjointUnitSubspace (C D : PresentableInfinityObject.{u})
    (w : PrRFunctorSpace D C _⦋0⦌) : SSet.{u + 1} :=
  (fullSubcomplexOnVertices (RightUnitCoslice C D w) (fun v ↦
    UnitMappingSpaceCondition (F := rightUnitLeftFunctor v)
      (G := rightVertexFunctor w) (rightUnitHom v)) : SSet.{u + 1})

/-- 概要：固定した元の右関手に対する随伴実単位の全部分複体は可縮。
方針：指定単位条件と始対象性の同値で頂点条件を置き換え、全境界を充填する。
規約：元の全関手圏の高次単体を保つ可縮性。
使われ方：随伴単位の選択に関する高次の一意性。 -/
lemma rightAdjointUnitSubspace_isContractibleKan (C D : PresentableInfinityObject.{u})
    (w : PrRFunctorSpace D C _⦋0⦌) : IsContractibleKan (RightAdjointUnitSubspace C D w) := by
  have hP : (fun v : RightUnitCoslice C D w _⦋0⦌ ↦
      UnitMappingSpaceCondition (F := rightUnitLeftFunctor v)
        (G := rightVertexFunctor w) (rightUnitHom v)) = IsInitialVertex :=
    funext (fun v ↦ propext (rightUnit_condition_iff_isInitial v))
  unfold RightAdjointUnitSubspace
  rw [hP]
  exact initialVertices_isContractibleKan (rightUnitCoslice_hasInitial C D w)

instance rightAdjointUnitSubspace_kanComplex (C D : PresentableInfinityObject.{u})
    (w : PrRFunctorSpace D C _⦋0⦌) : KanComplex (RightAdjointUnitSubspace C D w) :=
  (rightAdjointUnitSubspace_isContractibleKan C D w).kanComplex

/-- 概要：固定した元の右関手に対する随伴実単位の Kan 空間。
方針：同じ随伴単位の全部分複体の core を取る。
規約：元の実単位の core であり、随伴の証拠の離散集合ではない。
使われ方：両関手の写像空間の右射影の固定ファイバーとの比較。 -/
def RightAdjointUnitSpace (C D : PresentableInfinityObject.{u})
    (w : PrRFunctorSpace D C _⦋0⦌) : SSet.{u + 1} :=
  quasicategoryCore (RightAdjointUnitSubspace C D w)

/-- 概要：元の右関手を固定した随伴単位の core は可縮。
方針：全部分複体の Kan 性による core の厳密同型で可縮性を移す。
規約：モデル構造や同値の存在の追加仮定は使わない。
使われ方：元の右射影の高次ファイバーの可縮性を検証する比較先。 -/
lemma rightAdjointUnitSpace_isContractibleKan (C D : PresentableInfinityObject.{u})
    (w : PrRFunctorSpace D C _⦋0⦌) : IsContractibleKan (RightAdjointUnitSpace C D w) :=
  isContractibleKan_of_iso (quasicategoryCoreIsoOfKan _).symm
    (rightAdjointUnitSubspace_isContractibleKan C D w)

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
