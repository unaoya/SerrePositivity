module
public import SerrePositivity.InfinityCategories.Derived.DGWalkingHomDegreeExt
public import SerrePositivity.InfinityCategories.Derived.DGClosedCompositionLinear
public import SerrePositivity.InfinityCategories.DGNerve.StrictNatTrans

/-! # 自由 Hom の生成辺からの厳密 dg 自然変換

概要：二対象の成分と係数生成辺上の全次数の自然性から厳密 dg 自然変換を作る。
方針：各次数の外延性で単位と生成辺へ戻し、単位上の自然性を自動で証明する。
規約：閉零射上だけの通常の自然性へ弱めない。使われ方：閉前合成の全次数 prism。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded DGNerve HomologicalComplex
open scoped ZeroObject
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (M : Complex A)
variable (F G : DGFunctor A (DGWalkingHom.{u, v} A M) D)

/-- 生成係数の全次数の自然性から、自由 dg Hom 圏上の厳密自然変換を得る。 -/
def dgWalkingHomStrictNatTrans
    (t : ∀ x, zeroCycles (homObject A D (F.obj x) (G.obj x)))
    (h : ∀ k (a : M.X k),
      compose A (t (dgWalkingHomTarget A M)).val
        ((F.map (dgWalkingHomSource A M) (dgWalkingHomTarget A M)).f k
          ((dgWalkingHomGenerator A M).f k a)) (add_zero k) =
      compose A ((G.map (dgWalkingHomSource A M) (dgWalkingHomTarget A M)).f k
        ((dgWalkingHomGenerator A M).f k a))
          (t (dgWalkingHomSource A M)).val (zero_add k)) : StrictNatTrans F G where
  app := t
  naturality {x y} {k} a := by
    let L := ModuleCat.ofHom ((dgZeroPostcomposeLinear A D (t y).val k).comp
      ((F.map x y).f k).hom)
    let R := ModuleCat.ofHom ((dgZeroPrecomposeLinear A D (t x).val k).comp
      ((G.map x y).f k).hom)
    have hLR : L = R := by
      apply dgWalkingHomDegree_ext A M x y k
      · intro hxy
        subst y
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro b
        have hF := congrArg (fun f => f.f k b) (F.map_id x)
        have hG := congrArg (fun f => f.f k b) (G.map_id x)
        change (F.map x x).f k ((FreeDGCategory.unitInclusion A DGWalkingHomVertex
          (dgWalkingHomQuiver A M) x).f k b) = (eId (Complex A) (F.obj x)).f k b at hF
        change (G.map x x).f k ((FreeDGCategory.unitInclusion A DGWalkingHomVertex
          (dgWalkingHomQuiver A M) x).f k b) = (eId (Complex A) (G.obj x)).f k b at hG
        change compose A (t x).val _ _ = compose A _ (t x).val _
        exact (congrArg (fun v => compose A (t x).val v (add_zero k)) hF).trans
          ((dgZero_unit_naturality A D (t x).val k b).trans
            (congrArg (fun v => compose A v (t x).val (zero_add k)) hG.symm))
      · apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro b
        rcases x with ⟨x⟩
        rcases y with ⟨y⟩
        cases x <;> cases y
        all_goals first
        | exact h k b
        | have hz : IsZero ((0 : Complex A).X k) :=
            (HomologicalComplex.eval (ModuleCat A) (.up ℤ) k).map_isZero (isZero_zero _)
          have hb : b = 0 := (ModuleCat.subsingleton_of_isZero hz).elim _ _
          subst b
          simp [L, R, dgZeroPostcomposeLinear, dgZeroPrecomposeLinear,
            compose_zero, zero_compose]
    exact ConcreteCategory.congr_hom hLR a

end SerrePositivity.InfinityCategories
