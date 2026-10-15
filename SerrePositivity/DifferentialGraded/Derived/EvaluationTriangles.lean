module
public import SerrePositivity.DifferentialGraded.Derived.Triangulated
public import SerrePositivity.DifferentialGraded.Derived.Ring

/-! # 導来評価と一対象A比較の三角性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated

/-- 三段の関手合成の可換squareから、三角形の比較を得る。 -/
def mapTriangleTripleSquareIso {C K E J H : Type*}
    [Category* C] [Category* K] [Category* E] [Category* J] [Category* H]
    [HasShift C ℤ] [HasShift K ℤ] [HasShift E ℤ] [HasShift J ℤ] [HasShift H ℤ]
    (Q : C ⥤ K) (L : K ⥤ E) (G : E ⥤ H) (F : C ⥤ J) (q : J ⥤ H)
    [Q.CommShift ℤ] [L.CommShift ℤ] [G.CommShift ℤ] [F.CommShift ℤ] [q.CommShift ℤ]
    (α : (Q ⋙ L) ⋙ G ≅ F ⋙ q) [NatTrans.CommShift α.hom ℤ]
    (T : Triangle C) (T' : Triangle J) (e : F.mapTriangle.obj T ≅ T') :
    G.mapTriangle.obj (L.mapTriangle.obj (Q.mapTriangle.obj T)) ≅ q.mapTriangle.obj T' :=
  G.mapTriangle.mapIso ((Functor.mapTriangleCompIso Q L).symm.app T) ≪≫
    mapTriangleSquareIso (Q ⋙ L) G F q α T T' e

section General
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- 元の閉零圏から見た導来評価の比較。既存のshift構造を使用する。 -/
def moduleDerivedEvaluationHomotopyFacIso (x : D) :=
  Functor.isoWhiskerRight (moduleToHomotopyDerivedIso A D) (moduleDerivedEvaluation A D x) ≪≫
    eqToIso (moduleDerivedEvaluation_fac A D x)

instance moduleDerivedEvaluationHomotopyFacCommShift (x : D) :
    NatTrans.CommShift (moduleDerivedEvaluationHomotopyFacIso A D x).hom ℤ := by
  change NatTrans.CommShift
    (Functor.whiskerRight (moduleToHomotopyDerivedIso A D).hom (moduleDerivedEvaluation A D x) ≫
      (eqToIso (moduleDerivedEvaluation_fac A D x)).hom) ℤ
  apply NatTrans.CommShift.comp

/-- 導来評価は標準加群cone三角形を既存導来圏の標準cone三角形へ移す。 -/
def moduleDerivedConeTriangleEvaluationIso {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :=
  mapTriangleTripleSquareIso (moduleToHomotopy A D) (moduleHomotopyToDerivedClosed A D)
    (moduleDerivedEvaluation A D x) (moduleEvaluation A D x) (DerivedCategory.Q (C := ModuleCat A))
    (moduleDerivedEvaluationHomotopyFacIso A D x) (moduleConeTriangle A D f)
    (CochainComplex.mappingCone.triangle ((moduleEvaluation A D x).map f))
    (moduleConeTriangleEvaluationIso A D f x)

instance moduleDerivedEvaluationIsTriangulated (x : D) :
    (moduleDerivedEvaluation A D x).IsTriangulated where
  map_distinguished T hT := by
    change ∃ (T₀ : Triangle (ModuleHomotopyCategory A D))
      (_ : T ≅ (moduleHomotopyToDerivedClosed A D).mapTriangle.obj T₀),
        T₀ ∈ distTriang (ModuleHomotopyCategory A D) at hT
    obtain ⟨T₀, e₀, h₀⟩ := hT
    change ∃ (M N : ModuleCategory A D) (f : M ⟶ N), Nonempty
      (T₀ ≅ (moduleToHomotopy A D).mapTriangle.obj (moduleConeTriangle A D f)) at h₀
    obtain ⟨M, N, f, ⟨e₁⟩⟩ := h₀
    exact isomorphic_distinguished _
      (DerivedCategory.mappingCone_triangle_distinguished ((moduleEvaluation A D x).map f)) _
      ((moduleDerivedEvaluation A D x).mapTriangle.mapIso e₀ ≪≫
        (moduleDerivedEvaluation A D x).mapTriangle.mapIso
          ((moduleHomotopyToDerivedClosed A D).mapTriangle.mapIso e₁) ≪≫
        moduleDerivedConeTriangleEvaluationIso A D f x)
end General

section OneObject
variable (A : Type u) [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- 一対象Aの既存導来圏との比較同値はdistinguished三角形を保存する。 -/
instance ringDerivedEquivalenceIsTriangulated : (ringDerivedEquivalence A).functor.IsTriangulated :=
  moduleDerivedEvaluationIsTriangulated A PUnit.{1} PUnit.unit

instance ringDerivedEquivalenceInverseCommShift : (ringDerivedEquivalence A).inverse.CommShift ℤ :=
  Functor.CommShift.ofComp (ringDerivedEquivalence A).counitIso ℤ

instance ringDerivedEquivalenceCounitCommShift :
    NatTrans.CommShift (ringDerivedEquivalence A).counitIso.hom ℤ :=
  Functor.CommShift.ofComp_compatibility (ringDerivedEquivalence A).counitIso ℤ

instance ringDerivedEquivalenceInverseIsTriangulated :
    (ringDerivedEquivalence A).inverse.IsTriangulated :=
  (Functor.isTriangulated_iff_comp_right (ringDerivedEquivalence A).counitIso).2 inferInstance
end OneObject

end SerrePositivity.DifferentialGraded
