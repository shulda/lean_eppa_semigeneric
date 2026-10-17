import SemigenericEPPA.Algebra.RawDatum
import SemigenericEPPA.Algebra.Recenter
import SemigenericEPPA.Algebra.Gauge
import SemigenericEPPA.Algebra.CornerAmalgamation
import SemigenericEPPA.Algebra.CongruenceAction
import SemigenericEPPA.Structure.Language
import SemigenericEPPA.Structure.EffectiveColour
import SemigenericEPPA.Structure.Induced
import SemigenericEPPA.Structure.PartMatrix
import SemigenericEPPA.Structure.PartQuotient
import SemigenericEPPA.Structure.OnePointParts
import SemigenericEPPA.Bridge.CoherentEPPA

/-!
# Generalized semigeneric rectangle structures

Public root of the formalization.  Every verified module should eventually
be imported here, so that CI checks the whole project.

The target is the *explicit valuation proof* from the v0.8 manuscript.
The AllThoseEPPA dependency supplies partial-isomorphism/coherence vocabulary,
not the HKN EPPA theorem.
-/
