module

public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedConstantFiber

/-!
概要：一定の底での weighted cone simplex と標準左 Hom 比較の simplex を同定する。
方針：反対圏の右 Hom 比較を反転した simplex と頂点・Hom の全分岐で比較する。
規約：Hom の反転と端点の等号による移送を明示する。
使われ方：Kerodon §4.6.7、HTT 4.2.4.1 の具体的な fiber 射の同値性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet SimplicialThickening MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C]

/-- 概要：一定の底の cone simplex は反対圏の右 Hom の標準 simplex を反転したもの。
方針：頂点の反転を計算し、非定値 Hom には最小点と最大点の反転の式を使う。
規約：Kan 性・Hom の逆の選択を要求しない。
使われ方：HTT 4.2.4.1 の実際の fiber 比較と標準 Hom 比較の一致。 -/
lemma weightedConstantConeSimplex_eq (F : I ⥤ C) (x : C) (i : I) {n : ℕ}
    (s : (SimplicialCategory.sHom x (F.obj i)).op _⦋n⦌) :
    weightedConeSimplex F x
      (weightedNerveConstantDiagram (simplicialHomDiagram F x ⋙ SSet.opFunctor) i s) =
    coherentOppositeInverseSimplex
      (coherentHomComparisonSimplex (X := Opposite.op (F.obj i)) (Y := Opposite.op x)
        (SSet.opObjEquiv s)) := by
  have hn (a : Fin (n + 2)) :
      coherentHomComparisonObj (Opposite.op (F.obj i)) (Opposite.op x) a.rev =
        Opposite.op (Fin.cases x (fun _ ↦ F.obj i) a) := by
    induction a using Fin.cases (n := n + 1) with
    | zero => simp only [Fin.cases_zero, Fin.rev_zero, coherentHomComparisonObj_last]
    | succ a => simp only [Fin.cases_succ, Fin.rev_succ, coherentHomComparisonObj_cast]
  symm
  refine EnrichedFunctor.ext SSet
    (fun a ↦ congrArg Opposite.unop (hn a.as.down)) (fun a b ↦ ?_)
  rcases a with ⟨⟨a⟩⟩
  rcases b with ⟨⟨b⟩⟩
  change (((coherentReverseThickening (n + 1)).map ⟨ULift.up a⟩ ⟨ULift.up b⟩ ≫
      coherentHomComparisonHom (X := Opposite.op (F.obj i)) (Y := Opposite.op x)
        (SSet.opObjEquiv s) b.rev a.rev) ≫ 𝟙 _) ≫
      eqToHom (congrArg₂ (fun A B : C ↦ SimplicialCategory.sHom A B)
        (congrArg (fun z : Cᵒᵖ ↦ z.unop) (hn a)) (congrArg (fun z : Cᵒᵖ ↦ z.unop) (hn b))) =
    weightedConeHom F x
      (weightedNerveConstantDiagram (simplicialHomDiagram F x ⋙ SSet.opFunctor) i s) a b
  rw [Category.comp_id, Category.assoc]
  change (coherentReverseThickening (n + 1)).map ⟨ULift.up a⟩ ⟨ULift.up b⟩ ≫
      (coherentHomComparisonHom (X := Opposite.op (F.obj i)) (Y := Opposite.op x)
        (SSet.opObjEquiv s) b.rev a.rev ≫
        eqToHom (congrArg₂ (fun A B : Cᵒᵖ ↦ SimplicialCategory.sHom A B) (hn b) (hn a))) =
    weightedConeHom F x
      (weightedNerveConstantDiagram (simplicialHomDiagram F x ⋙ SSet.opFunctor) i s) a b
  induction a using Fin.cases (n := n + 1) <;>
    induction b using Fin.cases (n := n + 1)
  case zero.zero =>
    rw [coherentHomComparisonHom_transport
      (X := Opposite.op (F.obj i)) (Y := Opposite.op x) (SSet.opObjEquiv s)
      (Fin.rev_zero (n + 1)) (Fin.rev_zero (n + 1))
      (coherentHomComparisonObj_last (Opposite.op (F.obj i)) (Opposite.op x) n)
      (coherentHomComparisonObj_last (Opposite.op (F.obj i)) (Opposite.op x) n),
      coherentHomComparisonHom_last_last]
    simp only [← Category.assoc, comp_toUnit]
    rfl
  case succ.zero a =>
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    have h := Path.le (P.obj 0)
    change a.succ ≤ 0 at h
    simp at h
  case zero.succ b =>
    rw [coherentHomComparisonHom_transport
      (X := Opposite.op (F.obj i)) (Y := Opposite.op x) (SSet.opObjEquiv s)
      (Fin.rev_succ b) (Fin.rev_zero (n + 1))
      (coherentHomComparisonObj_cast (Opposite.op (F.obj i)) (Opposite.op x) b.rev)
      (coherentHomComparisonObj_last (Opposite.op (F.obj i)) (Opposite.op x) n),
      coherentHomComparisonHom_cast_last]
    rw [weightedConstantConeHom_zero_succ]
    simp only [← Category.assoc]
    congr 1
    congr 1
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    apply CategoryTheory.Functor.ext (fun k ↦ ?_)
    apply SimplicialThickening.Path.ext
    let hleft := congrArg
      (fun a : Fin (n + 2) ↦
        (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))) (Fin.rev_succ b)
    let hright := congrArg
      (fun a : Fin (n + 2) ↦
        (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))))
      (Fin.rev_zero (n + 1))
    change (((eqToHom (congrArg₂
      (fun A B : SimplicialThickening (ULift.{u} (Fin (n + 2))) ↦
        SimplicialCategory.sHom A B) hleft hright)).app d
      (((coherentReverseThickening (n + 1)).map
        ⟨ULift.up 0⟩ ⟨ULift.up b.succ⟩).app d P)).obj k).I = _
    rw [thickeningHom_transport_I hleft hright
      (((coherentReverseThickening (n + 1)).map
        ⟨ULift.up 0⟩ ⟨ULift.up b.succ⟩).app d P) k]
    rfl
  case succ.succ a b =>
    rw [coherentHomComparisonHom_transport
      (X := Opposite.op (F.obj i)) (Y := Opposite.op x) (SSet.opObjEquiv s)
      (Fin.rev_succ b) (Fin.rev_succ a)
      (coherentHomComparisonObj_cast (Opposite.op (F.obj i)) (Opposite.op x) b.rev)
      (coherentHomComparisonObj_cast (Opposite.op (F.obj i)) (Opposite.op x) a.rev),
      coherentHomComparisonHom_cast_cast]
    simp only [← Category.assoc, comp_toUnit]
    apply SSet.hom_ext
    rintro ⟨⟨d⟩⟩
    apply ConcreteCategory.hom_ext
    intro P
    change (eId SSet (F.obj i)).app (Opposite.op ⦋d⦌) PUnit.unit =
      PinchedHom.constant (SimplicialCategory.homEquiv' _ _ (F.map (𝟙 i))) d
    rw [F.map_id]
    simp only [SimplicialCategory.homEquiv', Equiv.trans_apply, eHomEquiv_id]
    exact unitHom_app_constant (eId SSet (F.obj i)) d


/-- 概要：構成済みの一定の底の fiber 射は標準の左 coslice Hom 比較に厳密に一致する。
方針：coslice の simplex の座標で検出し、coherent simplex 全体の一致を使う。
規約：順方向の実際の射を同定し、点ごとの逆射の選択は使わない。
使われ方：HTT 4.2.4.1 の実際の fiber 射の同値性の移送。 -/
lemma weightedConstantCosliceFiberMap_eq (F : I ⥤ C) (x : C) (i : I) :
    weightedConstantCosliceFiberMap F x i = coherentCosliceFiberComparison x (F.obj i) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s⟩
  apply Equiv.injective
    (cosliceFiberSimplexEquiv (coherentNerveVertex x) (coherentNerveVertex (F.obj i)) n)
  apply Subtype.ext
  change cosliceFiberSimplex n
      ((weightedConstantCosliceFiberMap F x i).app (Opposite.op ⦋n⦌) (ULift.up s)) =
    cosliceFiberSimplex n
      ((cosliceFiberSimplexEquiv (coherentNerveVertex x) (coherentNerveVertex (F.obj i)) n).symm
        ((pinchedLeftSimplexEquiv (coherentNerveVertex x) (coherentNerveVertex (F.obj i)) n)
          ((coherentLeftHomComparison x (F.obj i)).app (Opposite.op ⦋n⦌) (ULift.up s))))
  rw [cosliceFiberSimplex_equiv_symm]
  change cosliceFiberSimplex n
      ((weightedConstantCosliceFiberMap F x i).app (Opposite.op ⦋n⦌) (ULift.up s)) =
    pinchedLeftSimplexVal n
      ((coherentLeftHomComparison x (F.obj i)).app (Opposite.op ⦋n⦌) (ULift.up s))
  rw [weightedConstantCosliceFiberMap_simplex, coherentLeftHomComparison_simplex,
    weightedConstantConeSimplex_eq]

/-- 概要：局所 Kan 性の下で構成済みの一定の底の fiber 射はホモトピー同値。
方針：射そのものを標準左 Hom 比較に同定し、既証の同値性を移す。
規約：全ての豊穣 Hom の Kan 性以外に比較の同値性を仮定しない。
使われ方：HTT 4.2.4.1 の重み付き nerve と coherent な錐の fiber の同値。 -/
lemma weightedConstantCosliceFiberMap_homotopyEquivalence
    [∀ a b : C, KanComplex (SimplicialCategory.sHom a b)] (F : I ⥤ C) (x : C) (i : I) :
    IsSimplicialHomotopyEquivalence (weightedConstantCosliceFiberMap F x i) := by
  rw [weightedConstantCosliceFiberMap_eq]
  exact coherentCosliceFiberComparison_homotopyEquivalence x (F.obj i)

end SerrePositivity.InfinityCategories.HomotopyLimits
