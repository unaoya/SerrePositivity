module
public import SerrePositivity.HomologicalAlgebra.DoldKanGammaMap

/-!
概要：Γ と加法関手の交換同型が、元の鎖複体の全射に自然であること。
方針：Γ の指定余積包含と splitting の包含を同定し、各生成成分で比較する。
規約：交換同型の前向き射は指定余積比較のまま。
使われ方：HA 1.2.4、G10 の図式上の Dold–Kan 比較と係数射の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v u' v'
open CategoryTheory Limits AlgebraicTopology SimplicialObject Opposite
open AlgebraicTopology.DoldKan
namespace SerrePositivity.HomologicalAlgebra
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- Γ の splitting の包含は、各全射添字の指定余積包含そのもの。 -/
theorem gammaCofanInj (K : ChainComplex C ℕ) (a : SimplexCategoryᵒᵖ)
    (s : Splitting.IndexSet a) :
    ((Γ₀.splitting K).cofan a).inj s = Sigma.ι (Γ₀.Obj.summand K a) s := by
  change Sigma.ι (Γ₀.Obj.summand K s.1) (Splitting.IndexSet.id s.1) ≫
    Γ₀.Obj.map K s.e.op = _
  rw [Γ₀.Obj.map_on_summand₀ K (Splitting.IndexSet.id s.1)
    (show s.e ≫ 𝟙 s.1.unop = s.e.op.unop ≫ (Splitting.IndexSet.id s.1).e by
      change s.e ≫ 𝟙 _ = s.e ≫ 𝟙 _
      rfl), Γ₀.Obj.Termwise.mapMono_id]
  erw [Category.id_comp]
  rfl

/-- 元の鎖射の Γ 像は、各余積成分でその鎖射の成分そのもの。 -/
@[reassoc]
theorem gamma_ι_map {K L : ChainComplex C ℕ} (f : K ⟶ L)
    (a : SimplexCategoryᵒᵖ) (s : Splitting.IndexSet a) :
    Sigma.ι (Γ₀.Obj.summand K a) s ≫
      ((Abelian.DoldKan.Γ : ChainComplex C ℕ ⥤ SimplicialObject C).map f).app a =
    f.f s.1.unop.len ≫ Sigma.ι (Γ₀.Obj.summand L a) s := by
  rw [← gammaCofanInj, ← gammaCofanInj]
  exact (Γ₀.splitting K).ι_desc a _ s

/-- Γ 交換の指定同型は元の鎖複体の全射に自然。 -/
theorem gammaMapIso_naturality (F : C ⥤ D) [F.Additive]
    {K L : ChainComplex C ℕ} (f : K ⟶ L) :
    (Abelian.DoldKan.Γ : ChainComplex D ℕ ⥤ SimplicialObject D).map
        ((F.mapHomologicalComplex (.down ℕ)).map f) ≫ (gammaMapIso F L).hom =
      (gammaMapIso F K).hom ≫ Functor.whiskerRight
        ((Abelian.DoldKan.Γ : ChainComplex C ℕ ⥤ SimplicialObject C).map f) F := by
  apply NatTrans.ext
  funext a
  apply Sigma.hom_ext
  intro s
  change Sigma.ι (Γ₀.Obj.summand ((F.mapHomologicalComplex (.down ℕ)).obj K) a) s ≫
    ((Abelian.DoldKan.Γ : ChainComplex D ℕ ⥤ SimplicialObject D).map
      ((F.mapHomologicalComplex (.down ℕ)).map f)).app a ≫ sigmaComparison F (Γ₀.Obj.summand L a) =
    Sigma.ι _ s ≫ sigmaComparison F (Γ₀.Obj.summand K a) ≫ F.map _
  erw [gamma_ι_map_assoc, ι_comp_sigmaComparison, ι_comp_sigmaComparison_assoc,
    ]
  simp only [← F.map_comp]
  erw [gamma_ι_map]
  rw [F.map_comp]
  rfl

/-- 指定 Γ 比較は、加法関手間の自然変換にも自然。 -/
theorem gammaMapIso_functor_naturality {F G : C ⥤ D} [F.Additive] [G.Additive]
    (α : F ⟶ G) (K : ChainComplex C ℕ) :
    (Abelian.DoldKan.Γ : ChainComplex D ℕ ⥤ SimplicialObject D).map
        ((NatTrans.mapHomologicalComplex α (.down ℕ)).app K) ≫ (gammaMapIso G K).hom =
      (gammaMapIso F K).hom ≫ Functor.whiskerLeft
        ((Abelian.DoldKan.Γ : ChainComplex C ℕ ⥤ SimplicialObject C).obj K) α := by
  apply NatTrans.ext
  funext a
  apply Sigma.hom_ext
  intro s
  change Sigma.ι (Γ₀.Obj.summand ((F.mapHomologicalComplex (.down ℕ)).obj K) a) s ≫
    ((Abelian.DoldKan.Γ : ChainComplex D ℕ ⥤ SimplicialObject D).map
      ((NatTrans.mapHomologicalComplex α (.down ℕ)).app K)).app a ≫
        sigmaComparison G (Γ₀.Obj.summand K a) =
    Sigma.ι _ s ≫ sigmaComparison F (Γ₀.Obj.summand K a) ≫ α.app _
  erw [gamma_ι_map_assoc, ι_comp_sigmaComparison, ι_comp_sigmaComparison_assoc]
  exact (α.naturality (Sigma.ι (Γ₀.Obj.summand K a) s)).symm

end SerrePositivity.HomologicalAlgebra
