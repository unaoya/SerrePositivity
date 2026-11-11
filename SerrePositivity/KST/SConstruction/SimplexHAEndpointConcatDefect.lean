module
public import SerrePositivity.KST.SConstruction.SimplexHAChainLiftCondition
public import SerrePositivity.KST.SConstruction.SimplexHAOrderDimensionCast
public import SerrePositivity.KST.SConstruction.SerreCubeEndpointIndexCases
public import SerrePositivity.KST.SConstruction.SimplexHAZeroFaceAllDefect
public import SerrePositivity.KST.SConstruction.SimplexHAOneTensorDefect

/-! # 元の内部端点生成元の微分条件の小次元への帰着
概要：全小次元の実復元鎖射があれば、任意の内部零・一端点生成元の実微分差は零。
方針：零面は削除列の小次元鎖射、一面は左右の小次元鎖射の実 tensor 合成へ戻す。
規約：元の全因子・次数・次元移送を保持。使われ方：全次元の実 Hom 鎖射の強い帰納。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 全小次元の実復元鎖射があれば、任意の内部端点連結生成元の実微分差は零。 -/
lemma simplexHADegreeDefect_endpoint_concat_zero {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D N)
    (n m : ℕ) (i : SerreCubeGeneratorIndex n) (j : SerreCubeGeneratorIndex m) (ε : Bool)
    (v : Fin (n + 1 + m + 1) ↪o Fin (N + 1)) (b : Fin (N + 1))
    (hb : v (Fin.last (n + 1 + m)) < b)
    (hsmall : ∀ d < n + 1 + m, SimplexHAChainLiftExists A s d) (k : ℤ)
    (ha : serreCubeGeneratorDegree (n + 1 + m)
      (serreCubeGeneratorConcat (n + 1) (i, serreCubeGeneratorEndpointIndex ε) m j) = k) :
    simplexHADegreeDefect A s (n + 1 + m) v b hb k
      (eqToHom (congrArg (fun d => (serreCubeComplex A (n + 1 + m)).X d) ha)
        (serreCubeGenerator A (n + 1 + m)
          (serreCubeGeneratorConcat (n + 1) (i, serreCubeGeneratorEndpointIndex ε) m j))) = 0 := by
  cases ε
  · let p := n + m
    let q : Fin (p + 1) := ⟨m, by omega⟩
    let c := serreCubeGeneratorConcat n i m j
    let a := serreCubeInsertGeneratorIndex false p q c
    let a' := serreCubeGeneratorConcat (n + 1) (i, 0) m j
    have he : p + 1 = n + 1 + m := by omega
    have hi : HEq a a' := serreCubeGeneratorConcat_insert false n i m j
    let w := simplexHAOrderDimensionCast he.symm v
    have hw : w (Fin.last (p + 1)) < b :=
      lt_of_eq_of_lt (simplexHAOrderDimensionCast_last he.symm v) hb
    have ha₀ : serreCubeGeneratorDegree (p + 1) a = k :=
      (serreCubeGeneratorDegree_heq he a a' hi).trans ha
    have hc : serreCubeGeneratorDegree p c = k :=
      (serreCubeInsertGeneratorIndex_degree false p q c).symm.trans ha₀
    let u := simplexHADeleteVertexOrder p q w
    let hu := (w.monotone
      (Fin.le_last ((simplexHAFaceVertex p q).succAbove (Fin.last p)))).trans_lt hw
    obtain ⟨F, hF⟩ := hsmall p (by omega) u b hu
    have hd := simplexHADegreeDefect_zero_of_chain A s p u b hu F hF k
    have hz := ConcreteCategory.congr_hom hd
      (eqToHom (congrArg (fun d => (serreCubeComplex A p).X d) hc) (serreCubeGenerator A p c))
    let E : homObject A D (s.obj (u 0)) (s.obj b) ⟶ homObject A D (s.obj (w 0)) (s.obj b) :=
      eqToHom (congrArg (fun a => homObject A D (s.obj a) (s.obj b))
        (simplexHADeleteVertexOrder_first p q w))
    have h₀ : simplexHADegreeDefect A s (p + 1) w b hw k
        (eqToHom (congrArg (fun d => (serreCubeComplex A (p + 1)).X d) ha₀)
          (serreCubeGenerator A (p + 1) a)) = 0 :=
      (simplexHADegreeDefect_insert_zero A s p q c w b hw k hc).trans
        ((congrArg (fun x => E.f (k + 1) x) hz).trans (map_zero _))
    exact (simplexHADegreeDefect_generator_zero_heq A s he a a' hi w v
      (simplexHAOrderDimensionCast_heq he.symm v) b hw hb k ha₀ ha).mp h₀
  · obtain ⟨F, hF⟩ := hsmall n (by omega) (simplexHASplitLeft n m v)
      (simplexHASplitCut n m v) (simplexHASplitLeft_last_lt n m v)
    obtain ⟨G, hG⟩ := hsmall m (by omega) (simplexHASplitRight n m v) b
      (lt_of_eq_of_lt (simplexHASplitRight_last n m v) hb)
    have hk : serreCubeGeneratorDegree n i + serreCubeGeneratorDegree m j = k :=
      ((serreCubeGeneratorConcat_degree (n + 1) (i, 1) m j).trans
        (congrArg (· + serreCubeGeneratorDegree m j)
          (add_zero (serreCubeGeneratorDegree n i)))).symm.trans ha
    have hz := ConcreteCategory.congr_hom
      (simplexHADegreeDefect_one_tensor_zero A s n m v b hb F G hF hG k)
      (serreCubeTensorPair A n m (serreCubeGeneratorDegree n i) (serreCubeGeneratorDegree m j)
        k hk (serreCubeGenerator A n i) (serreCubeGenerator A m j))
    have ht := congrArg (fun x => simplexHADegreeDefect A s (n + 1 + m) v b hb k x)
      (serreCubeRightFace_tensor_generator A true n i m j k hk)
    exact ht.symm.trans hz

end SerrePositivity.KST.SConstruction
