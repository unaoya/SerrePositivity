# Standard S-linear interface: still open, do not count HT02 complete

The fixed R-linear comparison theorem is not by itself a proof that an unspecified S-linear comparison is canonical.
CompletedScalarModels identifies its source with the restriction of ordinary base change of ANY specified K-flat model q:P→K; no K-flat hypothesis on K.
ScalarModelNaturality must show normalization by Q(L⊗q) and compatibility with every actual commuting model map. It does not infer strict diagrams from objectwise resolutions.
ScalarRestrictionTotal gives the original S-linear target's underlying R-model, using restricted original component projections. Need its naturality after it passes.

Possible native ordinary S-linear comparison (not yet implemented):
1. Define the complex base-change unit K→Res(E K) termwise by extendRestrictScalarsAdj.unit. Chain condition is native unit naturality.
2. Apply the same unit rowwise; use Tot(row unit) followed by restrictionTotalIso.inv to obtain Tot K→Res(Tot(E rows K)).
3. Define E(Tot K)→Tot(E rows K) termwise by native module adjunction homEquiv.symm of step 2. Chain condition follows homEquiv naturality; no new S action on L.
4. Check L.comparison(Tot K) followed by restriction of step 3 equals tensorTotalComparison L K followed by Tot(row comparison), then restrictionTotalIso.inv. Use tensor coefficient naturality for augmentation L→single₀(S_R); its nonzero degree is zero, so the exchange sign becomes 1.
5. After finite S-completion, normalize by original units, using finiteDerivedCompletionRestrictionIso. Finite reflection gives uniqueness. Need rowwise model identifications and TotalQuasiIso under the proved uniform lower bound.

Limit: this route for a GIVEN strict K-flat row presentation is valid; existence of such a strict presentation for arbitrary X must not be inferred from exists_unbounded_baseChange_model objectwise. Either use a native actual presentation at the application, or supply a proven strict resolution. Do not silently weaken HT02 to K-flat inputs or put the canonical comparison's isomorphism into an assumption.

Private pending files: CosimplicialComparison (R-linear strict cosimplicial interface), TotalQuasiIso (uniform-bound row model transport), TensorCoefficientNaturality (augmentation comparison law).
